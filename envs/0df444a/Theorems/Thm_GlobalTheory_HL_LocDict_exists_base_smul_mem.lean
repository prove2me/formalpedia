-- Prove2me | Theorems.Thm_GlobalTheory_HL_LocDict_exists_base_smul_mem
-- name    : GlobalTheory.HL.LocDict.exists_base_smul_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:32:35.322902+00:00
-- url     : https://prove2.me/theorems/df396f3a-de39-484e-9369-23aaff341d37
-- title:
--   Loc Dict: exists base smul mem
-- statement:
--   The Loc Dict construction uses the exists base smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemLatIffMemLocP.lean#L185-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemLatIffMemLocP.lean#L185-L254

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemLatIffMemLocP
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.LocDict
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} (A : Places F E sig) {n : ℕ} (p : HeightOneSpectrum (𝓞 F))
include A

theorem GlobalTheory.HL.LocDict.exists_base_smul_mem (Λ : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = p.asIdeal →
      ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ Λ) :
    ∃ a : 𝓞 F, a ∉ p.asIdeal ∧ algebraMap (𝓞 F) (𝓞 E) a • x ∈ Λ := by sorry
