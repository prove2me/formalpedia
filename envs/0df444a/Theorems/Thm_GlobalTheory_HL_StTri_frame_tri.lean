-- Prove2me | Theorems.Thm_GlobalTheory_HL_StTri_frame_tri
-- name    : GlobalTheory.HL.StTri.frame_tri
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:45:56.394026+00:00
-- url     : https://prove2.me/theorems/9d2f92b1-7c1c-4c2e-9640-e8e082539bfe
-- title:
--   St Tri: frame tri
-- statement:
--   The St Tri construction uses the frame tri property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/GlobalFrameStabilizerActsUnitriangular.lean#L78-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/GlobalFrameStabilizerActsUnitriangular.lean#L78-L126

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_GlobalFrameStabilizerActsUnitriangular
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
noncomputable section
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.StTri

theorem GlobalTheory.HL.StTri.frame_tri {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : Places F E sig) {r n : ℕ} (p : HeightOneSpectrum (𝓞 F))
    (x : (Fin n → E) ≃ₗ[E] (Fin n → E))
    (xp : (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep)) (hext : A.Ext p x xp)
    (gG : Fin (r + 1) → Fin n → E) (gS : Fin (r + 1) → Fin n → (A.loc p).Ep)
    (u : Fin (r + 1) → (A.loc p).Ep) (hu : ∀ a, IsUnit (u a)) (heq : ∀ a, u a • gS a = A.bc p (gG a))
    (hstep : ∀ j : Fin (r + 1), xp (gS j) - gS j ∈ Submodule.span (A.loc p).Ep (gS '' {i | (i : ℕ) < j})) :
    ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧
      ∀ j, x (gG j) = ∑ i, s i j • gG i := by sorry
