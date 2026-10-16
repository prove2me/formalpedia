-- Prove2me | Theorems.Thm_MIPRE_Halting_tab_match
-- name    : MIPRE.Halting.tab_match
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:32:28.594982+00:00
-- url     : https://prove2.me/theorems/524f581d-f921-4797-87ff-92dae10f6c1a
-- title:
--   O2, the match: the doubled tabulation of the verifier a string denotes matches its doubled game
-- statement:
--   Fix a gap-preserving compression instance $G$ and a universal machine $U$. A bit string $x$ denotes the verifier $\mathcal V_x = \mathrm{Vof}(G, U, x)$: the compressed sampler $S^{\mathrm{compr}}_{\lambda_x}$ at the string's parameter $\lambda_x$ and the string's decider datum $\mathcal D_x$, run by $U$ inside the question-length check. At level $n$ its questions are $\mathbb F_2^{s(n)}$, $s(n)$ the sampler's dimension, and its answers the strings of length at most $T = \mathrm{ansBound}(x, n) = \mathrm{bound}_G(n + \lambda_x)$; it is $n$-bounded (`IsBounded n`) when for all $m \ge 2$, $s(m) \le m^n$ and its sampler and decider run within cost $m^n(|d|+1)^n$ on every input $(m, d)$, and its description has size at most $n$.
--
--   The doubled game $\mathcal V_x^{\mathrm{dbl}}(n, T)$ (`doubledGame`) is the synchronous game on $\mathrm{Bool} \times \mathbb F_2^{s(n)}$ with answers $\{0,1\}^{\le T}$: the pair $((\mathsf{false}, u), (\mathsf{true}, v))$ has the sampler's probability of $(u, v)$ and is accepted when the decider accepts $(n, \mathrm{bits}(u), \mathrm{bits}(v), a, b)$; every other pair has probability $0$ and is rejected. The description $\mathrm{tab}(x, n)$ (`GameData`) has indices $0, \dots, n_X$ and $0, \dots, n_A$; its game normalizes its weights and accepts the listed tuples except unequal answers to equal questions.
--
--   Assume $\mathcal V_x$ is $n$-bounded. Then there are bijections $e_X : \mathrm{Fin}(n_X + 1) \simeq \mathrm{Bool} \times \mathbb F_2^{s(n)}$ and $e_A : \mathrm{Fin}(n_A + 1) \simeq \{0,1\}^{\le T}$ such that, for all $i, j, k, l$,
--
--   $$ \mu_{\mathrm{tab}(x,n)}(i, j) = \mu^{\mathrm{dbl}}_{\mathcal V_x}(e_X i, e_X j),\quad D_{\mathrm{tab}(x,n)}(i, j, k, l) = D^{\mathrm{dbl}}_{\mathcal V_x}(e_X i, e_X j, e_A k, e_A l). $$
--
--   The match of obligation O2 of the halting reduction: it delivers the relabelings, not only the value, and needs no synchronicity of the decider, a description's forced rejections sitting on the diagonal, which the doubled distribution avoids; `tab_value` derives the value.
--
--   **Formalization Note**. The statement is `MIPRE.Halting.tab_match`; the existential is over the two relabelings `eX`, `eA` with the types displayed above. `(tab G U x n).game` is `HaltingGameValue.GameData.game`, `doubledGame n T` is `((Vof G U x).game n T).doubled`; the clauses compare their fields `μ` and `D`. The only hypothesis is `IsBounded n`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Instantiation.lean#L580-L610; the match of obligation O2 of blueprint thm:halting, per the module docstring; no blueprint label is attached to this declaration

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

theorem MIPRE.Halting.tab_match (x : BitStr) (n : ℕ) (hb : (Vof G U x).IsBounded n) :
    ∃ (eX : Fin ((tab G U x n).nX + 1) ≃ Bool × (Vof G U x).Questions n)
      (eA : Fin ((tab G U x n).nA + 1) ≃ Verifier.Answers (ansBound G x n)),
      (∀ i j, (tab G U x n).game.μ i j
        = ((Vof G U x).doubledGame n (ansBound G x n)).μ (eX i) (eX j)) ∧
      (∀ i j k l, (tab G U x n).game.D i j k l
        = ((Vof G U x).doubledGame n (ansBound G x n)).D (eX i) (eX j) (eA k) (eA l)) := by sorry
