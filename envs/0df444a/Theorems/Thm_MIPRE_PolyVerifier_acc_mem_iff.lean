-- Prove2me | Theorems.Thm_MIPRE_PolyVerifier_acc_mem_iff
-- name    : MIPRE.PolyVerifier.acc_mem_iff
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:26:29.996277+00:00
-- url     : https://prove2.me/theorems/13c4477e-2c60-40de-a0ac-5377964779b1
-- title:
--   Reading back the tabulated acceptance list of a polynomial-time verifier
-- statement:
--   Let $V$ be a polynomial-time verifier, $z$ an input with `V.Efficient z`, and let $i, j$ range over `Fin ((V.tab z).nX + 1)` and $k, l$ over `Fin ((V.tab z).nA + 1)`, the question and answer indices of the table `V.tab z`. The acceptance list `(V.tab z).acc` is a list of quadruples of natural numbers: for each quadruple $(x, y, a, b)$ of strings of length at most $B(z) = P(|z|)$ on which the budgeted decider run returns `true` — `Machine.runForD` on `encode (z, x, y, a, b)` under the budget $P(|z| + |x| + |y| + |a| + |b|)$ returns `some (encode true)` — it contains $(\mathrm{qIdx}(\mathrm{false}, x), \mathrm{qIdx}(\mathrm{true}, y), \mathrm{idxOf}(a), \mathrm{idxOf}(b))$, where $\mathrm{qIdx}(t, x) = \mathrm{idxOf}(x) + N\cdot[t]$ and $N$ is the number of strings of length at most $B(z)$. `V.eX z` is the equivalence from question indices to tagged strings `Bool × Answers (B z)` and `V.eA z` the one from answer indices to `Answers (B z)`. `V.Accepts z x y a b` means that the decider halts on `encode (z, x, y, a, b)` with output `encode true`. Then
--
--   $$\big((i, j, k, l) \in (V.\mathrm{tab}\ z).\mathrm{acc}\big) \iff \Big((e_X\, i)_1 = \mathrm{false}\ \wedge\ (e_X\, j)_1 = \mathrm{true}\ \wedge\ V.\mathrm{Accepts}\ z\ (e_X\, i)_2\ (e_X\, j)_2\ (e_A\, k)\ (e_A\, l)\Big),$$
--
--   where the indices are cast to natural numbers on the left and the tagged questions and answers are read as their underlying bit strings on the right.
--
--   This is the acceptance half of the correspondence between the table and the doubled game $G_z$; `D_clause` is its restatement at the level of the decision predicates, and `quantumValue_tab` follows.
--
--   **Formalization Note** Membership is list membership of the tuple `((i : ℕ), (j : ℕ), (k : ℕ), (l : ℕ))` in `(V.tab z).acc`, which is `accListLE (V.B z) (qIdx (V.B z) false) (qIdx (V.B z) true) (accC (encode V.decider) V.bound z)`. The projections `.1`, `.2.1` and `.1` extract the tag, the string of a tagged question and the string of an answer. The equivalences `eX`, `eA` are noncomputable. The hypothesis `h : V.Efficient z` is required; `z` is implicit and `V` a section variable.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/ClassMIPStarTab.lean#L475-L500

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
import Definitions.Def_MIPRE_Foundations_ClassMIPStar
import Definitions.Def_MIPRE_Foundations_Cost_BoundedEval
import Definitions.Def_MIPRE_Foundations_Halting_Tabulate
import Definitions.Def_MIPRE_Foundations_ClassMIPStarTab

open MIPRE
open MIPRE.PolyVerifier
open MIPRE.Cost MIPRE.Verifier
open HaltingGameValue (GameData)
variable (V : PolyVerifier)

theorem MIPRE.PolyVerifier.acc_mem_iff {z : BitStr} (h : V.Efficient z) (i j : Fin ((V.tab z).nX + 1))
    (k l : Fin ((V.tab z).nA + 1)) :
    ((i : ℕ), (j : ℕ), (k : ℕ), (l : ℕ)) ∈ (V.tab z).acc
      ↔ ((V.eX z i).1 = false ∧ (V.eX z j).1 = true ∧
          V.Accepts z (V.eX z i).2.1 (V.eX z j).2.1 (V.eA z k).1 (V.eA z l).1) := by sorry
