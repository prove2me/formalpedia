-- Prove2me | Theorems.Thm_MIPRE_Halting_accL_mem_iff
-- name    : MIPRE.Halting.accL_mem_iff
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:38:30.105994+00:00
-- url     : https://prove2.me/theorems/24581012-3d74-43cf-877e-5c326b9294f1
-- title:
--   The acceptance table of the tabulation `tabL`, read back through the relabelings of questions and answers
-- statement:
--   Fix a gap-preserving compression $G$ and an efficient universal machine $U$. A bit string $x$ denotes the verifier $\mathcal V_x$ = `Vof G U x` (as in `mu_clauseL`; $\lambda_x$ = `descLam x` is its parameter), whose decider $\mathcal D_x$ accepts $(n, x', y', a, b)$ when its program halts on the encoded tuple with output $\mathrm{encode}(\mathtt{true})$; `ansBound G x n` is the answer-length cut. The tabulation `tabL G U x n` is the `GameData` describing the $n$-th game of $\mathcal V_x$ on the doubled question set (`mu_clauseL`); its field $\mathrm{acc}$ is the list of accepted index tuples $(i, j, k, l)$. The relabeling $e_X$ = `eXofL G U x n` : $\mathrm{Fin}(n_X + 1) \simeq \mathrm{Bool} \times \mathbb F_2^{s(n)}$ reads an index as a tag bit followed by the coordinates of a question; $e_A$ = `eAofL G U x n` : $\mathrm{Fin}(n_A + 1) \simeq \mathrm{Answers}(\mathrm{ansBound}(x, n))$ sends $k$ to the $k$-th string of the enumeration `Data.bitStrsLE T` of the bit strings of length at most $T$, by increasing length; $\mathrm{bits}(q)$ = `CL.toBits q` is the bit string of the coordinates of $q \in \mathbb F_2^{s(n)}$.
--
--   Assume (hb) `(Vof G U x).IsBounded (descLam x)`, that $\mathcal V_x$ is bounded by the string's own parameter, and (hn) $2 \le n$. Then for all $i, j \in \mathrm{Fin}(n_X + 1)$ and $k, l \in \mathrm{Fin}(n_A + 1)$:
--
--   $$ (i, j, k, l) \in \mathrm{acc}(\mathrm{tabL}(x, n)) \iff \mathrm{tag}(e_X i) = \mathtt{false} \;\wedge\; \mathrm{tag}(e_X j) = \mathtt{true} \;\wedge\; \mathcal D_x\ \text{accepts}\ \bigl(n,\ \mathrm{bits}(e_X i),\ \mathrm{bits}(e_X j),\ e_A(k),\ e_A(l)\bigr). $$
--
--   This is the acceptance half of the match `tabL_match`; the distribution half is `mu_clauseL`.
--
--   **Formalization Note**. The theorem is `MIPRE.Halting.accL_mem_iff`, with $G$, $U$ explicit; the tuple on the left is `((i : ℕ), (j : ℕ), (k : ℕ), (l : ℕ))` and the right-hand side is `(eXofL G U x n i).1 = false ∧ (eXofL G U x n j).1 = true ∧ (Vof G U x).decider.Accepts n (CL.toBits (eXofL G U x n i).2) (CL.toBits (eXofL G U x n j).2) (eAofL G U x n k).1 (eAofL G U x n l).1`. The table `acc` is `Verifier.accListW` over the tagged indexings with the test `accOfL`, one run of the decider under the budget $n^{\lambda_x}(|d| + 1)^{\lambda_x}$ (`Machine.runForD`); `hb` and `hn` make that budgeted run agree with acceptance, a $\Sigma_1$ statement (`accOfL_iff`, the budget lemma the module docstring says is swapped relative to `Instantiation.lean`).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Paper/TabulateL.lean#L299-L342; internal lemma of the tabulation of the halting reduction along the paper's route (the game the search branch of the paper-route decider tests)

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Computability.Halting
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecBasis
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.RE
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.UnitaryGroup
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
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawInt
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_ValueApprox
import Definitions.Def_MIPRE_Foundations_ValueApprox_Cayley
import Definitions.Def_MIPRE_Foundations_ValueApprox_Projective
import Definitions.Def_MIPRE_Foundations_ValueApprox_Gaussian
import Definitions.Def_MIPRE_Foundations_ValueApprox_Norms
import Definitions.Def_MIPRE_Foundations_ValueApprox_Dense
import Definitions.Def_MIPRE_Foundations_ValueApprox_Strategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_HaltingGameValue
import Definitions.Def_MIPRE_Foundations_GameDescription
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawStrategy
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawSemantics
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawComplete
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawPrimrec
import Definitions.Def_MIPRE_Foundations_ValueApprox_RE
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
import Definitions.Def_MIPRE_Foundations_ClassMIPStarComputable
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
import Definitions.Def_MIPRE_Foundations_Halting_Paper_TabulateL

open MIPRE
open MIPRE.Halting
open MIPRE.Cost
open HaltingGameValue (GameData)
variable (G : GapCompression) (U : UniversalMachine)

theorem MIPRE.Halting.accL_mem_iff (x : BitStr) (n : ℕ) (hb : (Vof G U x).IsBounded (descLam x)) (hn : 2 ≤ n)
    (i j : Fin ((tabL G U x n).nX + 1)) (k l : Fin ((tabL G U x n).nA + 1)) :
    ((i : ℕ), (j : ℕ), (k : ℕ), (l : ℕ)) ∈ (tabL G U x n).acc
      ↔ ((eXofL G U x n i).1 = false ∧ (eXofL G U x n j).1 = true ∧
          (Vof G U x).decider.Accepts n (CL.toBits (eXofL G U x n i).2)
            (CL.toBits (eXofL G U x n j).2) (eAofL G U x n k).1 (eAofL G U x n l).1) := by sorry
