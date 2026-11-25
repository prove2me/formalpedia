-- Prove2me | Theorems.Thm_GlobalTheory_SW_TwistBound_exists_moved
-- name    : GlobalTheory.SW.TwistBound.exists_moved
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:24:28.314795+00:00
-- url     : https://prove2.me/theorems/0ed66d88-5189-4e76-9ef4-d5aa40967b68
-- title:
--   Twist Bound: exists moved
-- statement:
--   The Twist Bound construction uses the exists moved property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/TwistedSiegelWeilDifferenceBounded.lean#L82-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/TwistedSiegelWeilDifferenceBounded.lean#L82-L123

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClsAndStab
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionSiegelParabolicExplicitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelWeilDifferenceAutomorphyLinearityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelWeilDifferenceInvariantNormBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsRationalMatrixMoveAdmissibleUniformLevelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistedSiegelWeilDifferenceBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.TwistBound
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}

theorem GlobalTheory.SW.TwistBound.exists_moved (hΨ : IsType Ψ) (hn : Even n) (hN : 4 * N < n) {M : ℕ} (hM : 0 < M)
    {φ : Fam E n N} (hφ : ∀ Λ ∈ Vset E n M, IsSB (φ Λ)) {a : Matrix (Fin N) (Fin N) E}
    (ha : a.det ≠ 0) (hψ : ∀ Λ ∈ Vset E n M, IsSB fun x => φ Λ (x * a))
    {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) : ∃ Z' ∈ Hn Ψ N,
      swd Ψ M (fun Λ x => φ Λ (x * a)) Z' 0 0 = swd Ψ M φ Z 0 0 ∧
        detIm Z' = |((Algebra.norm ℚ a.det : ℚ) : ℝ)| * detIm Z := by sorry
