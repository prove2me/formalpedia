-- Prove2me | Theorems.Thm_GlobalTheory_HL_StrongSt_strong_approx_stab
-- name    : GlobalTheory.HL.StrongSt.strong_approx_stab
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:05:10.764873+00:00
-- url     : https://prove2.me/theorems/5abe7db4-e9b3-5ba2-9fde-c3d3d752b379
-- title:
--   Strong St: strong approx stab
-- statement:
--   The Strong St construction uses the strong approx stab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/StrongApproxStab.lean#L66-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/StrongApproxStab.lean#L66-L131

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PatternUnitriangularStrongApproximationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LocalCommonStabiliserBlockUnitriangularOnFrameStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BlockUnitriangularRationalFromCommonStabiliserStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameMatrixCloseGivesLatticeCloseIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StrongApproxStab
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.StrongSt

theorem GlobalTheory.HL.StrongSt.strong_approx_stab : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ Λ : G.Lt, Submodule.IsLattice E Λ → ∀ c : ∀ p, ((A.loc p).Fp)ˣ, {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite → ∀ n : ∀ p, (G.S p).GLV, (∀ p, n p ∈ (G.S p).St) → {p | n p ∉ (G.S p).K0}.Finite → ∃ g ∈ G.St, ∀ p g', A.Ext p g g' → (n p)⁻¹ * g' ∈ (G.S p).K0 ∧ ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, (n p).symm (g' x) - x = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) • y := by sorry
