-- Prove2me | Theorems.Thm_MIPRE_Verifier_not_isBounded_iff_exists
-- name    : MIPRE.Verifier.not_isBounded_iff_exists
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:38:33.446168+00:00
-- url     : https://prove2.me/theorems/cdfb2648-da44-498f-9464-0c94f7323fe6
-- title:
--   $\lambda$-boundedness of a verifier fails exactly when some finite witness of a violation exists
-- statement:
--   Let $\mathcal V$ be a normal form verifier with $\ell$ levels (`Verifier ℓ`): a sampler $\mathcal S$ with program $\mathcal S.\mathrm{prog}$ and dimension function $s(n)$ = `V.sampler.dim n`, and a decider $\mathcal D$ with program $\mathcal D.\mathrm{prog}$; $|\mathcal V|$ = `V.size` is the larger of the sizes of the two programs. $\mathcal V$ is $\lambda$-bounded (`V.IsBounded lam`, blueprint `def:lambda-bounded`) when for every $n \ge 2$: $s(n) \le n^\lambda$, and both programs halt within cost $n^\lambda (|d| + 1)^\lambda$ on every input $\mathtt{cons}(\mathrm{encode}\ n, d)$, well formed or not (`TimeBoundAt n (n ^ lam) lam`); and $|\mathcal V| \le \lambda$. A bound violation witness (`V.BoundViolation lam w`) is a pair of data $w = (w_1, w_2)$ such that, with $m$ = `Data.natOf w₁` the number the datum $w_1$ denotes (its canonical binary reading, $0$ for a non-numeral) and $\beta = m^\lambda (|w_2| + 1)^\lambda$ = `boundBudget lam m w₂`: either $|\mathcal V| > \lambda$, or $2 \le m$ and one of: $s(m) > m^\lambda$; $\mathcal S.\mathrm{prog}$ does not halt within cost $\beta$ on $\mathtt{cons}(\mathrm{encode}\ m, w_2)$; $\mathcal D.\mathrm{prog}$ does not halt within cost $\beta$ on $\mathtt{cons}(\mathrm{encode}\ m, w_2)$.
--
--   For every $\lambda \in \mathbb N$:
--
--   $$ \neg\,\bigl(\mathcal V \text{ is } \lambda\text{-bounded}\bigr) \iff \exists\, w \in \mathrm{Data} \times \mathrm{Data},\ \mathrm{BoundViolation}_{\mathcal V}(\lambda, w). $$
--
--   Each clause of $\lambda$-boundedness is universally quantified, so its negation is a search, and this lemma says what the search looks for. It is the characterization behind `Verifier.rePred_not_isBounded` (blueprint `lem:bounded-violation-re`): the violation is recursively enumerable because each witness test is decidable.
--
--   **Formalization Note**. The theorem is `MIPRE.Verifier.not_isBounded_iff_exists` for `{ℓ : ℕ} (V : Verifier ℓ) (lam : ℕ)`. The index is carried as a datum `w.1` and read by `Data.natOf` (the docstring: so that the encoding the time bounds prepend to their input is primitive recursive in the witness). `HaltsWithin p x k` is `∃ r t, t ≤ k ∧ Eval [x] p r t`; `BoundViolation lam w` is literally `¬ V.size ≤ lam ∨ (2 ≤ m ∧ (¬ V.sampler.dim m ≤ m ^ lam ∨ ¬ HaltsWithin V.sampler.prog (.cons (encode m) w.2) (boundBudget lam m w.2) ∨ ¬ HaltsWithin V.decider.prog (.cons (encode m) w.2) (boundBudget lam m w.2)))` with `m = Data.natOf w.1`. No computability hypothesis on $\mathcal V$ is needed.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Semidecider.lean#L194-L232; blueprint lem:bounded-violation-re

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
import Definitions.Def_MIPRE_Foundations_Halting_CostBudget
import Definitions.Def_MIPRE_Foundations_Halting_Instantiation
import Definitions.Def_MIPRE_Foundations_Halting_Serial
import Definitions.Def_MIPRE_Foundations_Halting_Semidecider

open MIPRE
open MIPRE.Verifier
open MIPRE.Cost
open HaltingGameValue (GameData)
variable {ℓ : ℕ} (V : Verifier ℓ)

theorem MIPRE.Verifier.not_isBounded_iff_exists (lam : ℕ) :
    ¬ V.IsBounded lam ↔ ∃ w : Data × Data, V.BoundViolation lam w := by sorry
