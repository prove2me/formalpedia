-- Prove2me | Theorems.Thm_GlobalTheory_HL_EichlerParams_local_choice
-- name    : GlobalTheory.HL.EichlerParams.local_choice
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:58:46.457629+00:00
-- url     : https://prove2.me/theorems/5636f851-e6db-59bc-873c-9080b61901c1
-- title:
--   Eichler Params: local choice
-- statement:
--   The Eichler Params construction uses the local choice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianSymplecticBasisLocalExtension.lean#L131-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianSymplecticBasisLocalExtension.lean#L131-L171

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StrongApproximationAdditiveQuadraticExtensionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemCoord
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsSmulIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianSymplecticBasisLocalExtension
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
open GlobalTheory.HL.SAN
noncomputable section
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.EichlerParams
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
variable {R : Type} [CommRing R] [Algebra K R] [TopologicalSpace R]
variable (L : LocE K R)

theorem GlobalTheory.HL.EichlerParams.local_choice {N r : ℕ} (Hm : Matrix (Fin N) (Fin N) R) (X Y : Fin r → Fin N → R)
    (T : Finset (Fin r)) (up : Fin N → R)
    (horth : ∀ a ∈ T, hf L Hm up (X a) = 0 ∧ hf L Hm up (Y a) = 0)
    {e d' : K} (he : e ∈ 𝒪[K]) (he0 : e ≠ 0) (hd' : d' ∈ 𝒪[K])
    (bH : ∀ i j, Sm L e⁻¹ (Hm i j)) (bX : ∀ a j, Sm L e⁻¹ (X a j)) (bY : ∀ a j, Sm L e⁻¹ (Y a j))
    (bu : ∀ j, Sm L e⁻¹ (up j)) (v : Fin N → R) (hv : ∀ j, Sm L (2 * d' * e ^ 5) (v j - up j)) :
    (∀ j, Sm L (2 * d') (piL L Hm X Y T v j - up j)) ∧
      Sm L (2 * d') (hf L Hm (piL L Hm X Y T v) (piL L Hm X Y T v) - hf L Hm up up) := by sorry
