-- Prove2me | Theorems.Thm_MIPRE_Halting_acc_mem_iff
-- name    : MIPRE.Halting.acc_mem_iff
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:32:51.168856+00:00
-- url     : https://prove2.me/theorems/65e4b9f2-8aa9-42e7-9b78-be2d3432a35a
-- title:
--   The tabulated acceptance table of the verifier a string denotes, read back on the doubled game
-- statement:
--   Fix a gap-preserving compression instance $G$ and a universal machine $U$. A bit string $x$ denotes the verifier $\mathcal V_x = \mathrm{Vof}(G, U, x)$: the compressed sampler $S^{\mathrm{compr}}_{\lambda_x}$ at the parameter $\lambda_x$ the string carries, and the string's decider datum $\mathcal D_x$, run by $U$ inside the question-length check, which together form its decider $\mathcal D_{\mathcal V_x}$. At level $n$ its questions are $\mathbb F_2^{s(n)}$, $s(n)$ the sampler's dimension, and its answers the strings of length at most $T = \mathrm{ansBound}(x, n) = \mathrm{bound}_G(n + \lambda_x)$. It is $n$-bounded (`IsBounded n`) when for all $m \ge 2$, $s(m) \le m^n$ and its sampler and decider run within cost $m^n(|d|+1)^n$ on every input $(m, d)$, and its description has size at most $n$.
--
--   $\mathrm{tab}(x, n)$ is a game description (`GameData`) of this game with doubled questions: question indices $0, \dots, n_X$, $n_X + 1 = 2^{s(n)+1}$, answer indices $0, \dots, n_A$, one per string of length at most $T$, and an acceptance list $\mathrm{acc}$ of tuples of naturals, with relabelings $e_X : \mathrm{Fin}(n_X + 1) \simeq \mathrm{Bool} \times \mathbb F_2^{s(n)}$ (a tag and a point) and $e_A : \mathrm{Fin}(n_A + 1) \simeq \{0,1\}^{\le T}$.
--
--   Assume $\mathcal V_x$ is $n$-bounded. For all question indices $i, j$ and answer indices $k, l$,
--
--   $$ (i, j, k, l) \in \mathrm{acc}(\mathrm{tab}(x, n)) \iff \mathrm{tag}(e_X i) = \mathsf{false} \wedge \mathrm{tag}(e_X j) = \mathsf{true} \wedge \mathcal D_{\mathcal V_x}\ \text{accepts}\ \bigl(n,\ \mathrm{bits}(\mathrm{pt}(e_X i)),\ \mathrm{bits}(\mathrm{pt}(e_X j)),\ e_A k,\ e_A l\bigr), $$
--
--   where a decider accepts an input when it halts on its encoding with output $1$ (`Decider.Accepts`), and $\mathrm{bits}$ lists the coordinates of a vector.
--
--   Acceptance clause of the tabulation obligation O2 of the halting reduction; with `mu_clause` it yields `tab_match`.
--
--   **Formalization Note**. The statement is `MIPRE.Halting.acc_mem_iff`. `tab G U x n` is `tabOf` on the encoded sampler and wrapped-decider programs of `Vof G U x`, the tabulated dimension, the cut `ansBound G x n` and `G.deg`; `acc` is the list `accListW`; `i j k l` are cast to `ℕ`; `(eXof … i).1`/`.2` are the tag and point and `(eAof … k).1` the string. The only hypothesis is `(Vof G U x).IsBounded n`; per the module docstring the match could not hold of every string, acceptance being $\Sigma_1$.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Instantiation.lean#L537-L578; internal lemma of the tabulation (obligation O2) of blueprint thm:halting, per the module docstring; no blueprint label is attached to this declaration

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Halting
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecBasis
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.RE
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_HaltingGameValue
import Definitions.Def_MIPRE_Foundations_GameDescription
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Cost_Kleene
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Partrec
import Definitions.Def_MIPRE_Foundations_Cost_Partrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Semidecide
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Halting_Freeze
import Definitions.Def_MIPRE_Foundations_Halting_Classes
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Halting_Wrapper
import Definitions.Def_MIPRE_Foundations_Halting_Enumerate
import Definitions.Def_MIPRE_Foundations_Cost_BoundedEval
import Definitions.Def_MIPRE_Foundations_Halting_Tabulate
import Definitions.Def_MIPRE_Foundations_Cost_BitQuery
import Definitions.Def_MIPRE_Foundations_Cost_Succinct
import Definitions.Def_MIPRE_Foundations_Cost_Clocked
import Definitions.Def_MIPRE_Foundations_Cost_Threshold
import Definitions.Def_MIPRE_Foundations_Compression
import Definitions.Def_MIPRE_Foundations_Halting_Instantiation

open MIPRE
open MIPRE.Halting
open MIPRE.Cost
open HaltingGameValue (GameData)
variable (G : GapCompression) (U : UniversalMachine)

theorem MIPRE.Halting.acc_mem_iff (x : BitStr) (n : ℕ) (hb : (Vof G U x).IsBounded n)
    (i j : Fin ((tab G U x n).nX + 1)) (k l : Fin ((tab G U x n).nA + 1)) :
    ((i : ℕ), (j : ℕ), (k : ℕ), (l : ℕ)) ∈ (tab G U x n).acc
      ↔ ((eXof G U x n i).1 = false ∧ (eXof G U x n j).1 = true ∧
          (Vof G U x).decider.Accepts n (CL.toBits (eXof G U x n i).2)
            (CL.toBits (eXof G U x n j).2) (eAof G U x n k).1 (eAof G U x n l).1) := by sorry
