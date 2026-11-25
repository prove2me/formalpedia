-- Prove2me | Theorems.Thm_GlobalTheory_HL_PlacesInt_mem_O_iff
-- name    : GlobalTheory.HL.PlacesInt.mem_O_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:12:44.30879+00:00
-- url     : https://prove2.me/theorems/7b29a64a-ce11-468a-902a-e1498a45d139
-- title:
--   Places Int: mem O iff
-- statement:
--   The Places Int construction uses the mem O iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsIntegralOfQuad.lean#L125-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsIntegralOfQuad.lean#L125-L147

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.PlacesInt
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}

theorem GlobalTheory.HL.PlacesInt.mem_O_iff (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) (x : E) (t n : F)
    (ht : algebraMap F E t = x + sig x) (hn : algebraMap F E n = x * sig x) :
    (A.loc p).ιE x ∈ (A.L p).O ↔ p.valuation F t ≤ 1 ∧ p.valuation F n ≤ 1 := by sorry
