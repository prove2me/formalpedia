-- Prove2me | Theorems.Thm_GlobalTheory_HL_StrongApprox_decomp
-- name    : GlobalTheory.HL.StrongApprox.decomp
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:16:02.911022+00:00
-- url     : https://prove2.me/theorems/f5e6f8c2-c8b0-53bb-81e9-43ce045d7404
-- title:
--   Strong Approx: decomp
-- statement:
--   The Strong Approx construction uses the decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/StrongApproximationAdditiveQuadraticExtension.lean#L277-L303
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/StrongApproximationAdditiveQuadraticExtension.lean#L277-L303

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StrongApproximationAdditiveQuadraticExtension
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.StrongApprox
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E}

theorem GlobalTheory.HL.StrongApprox.decomp (A : Places F E sig) (d : E) (hd : sig d = -d) (hd0 : d ≠ 0) (p : HeightOneSpectrum (𝓞 F))
    (y : (A.loc p).Ep) : ∃ a b : (A.loc p).Fp,
      y = algebraMap _ _ a + algebraMap _ _ b * (A.loc p).ιE d ∧
      algebraMap _ _ a = (A.loc p).ιE (algebraMap F E 2⁻¹) * (y + (A.L p).cj y) ∧
      (y ∈ (A.L p).O → (A.loc p).ιE d⁻¹ ∈ (A.L p).O → (A.loc p).ιF 2⁻¹ ∈ 𝒪[(A.loc p).Fp] →
        a ∈ 𝒪[(A.loc p).Fp] ∧ b ∈ 𝒪[(A.loc p).Fp]) := by sorry
