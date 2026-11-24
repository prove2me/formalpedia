-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_adele_neg_integral
-- name    : GlobalTheory.AdLat.adele_neg_integral
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:53:58.408689+00:00
-- url     : https://prove2.me/theorems/809515ec-5d53-47a2-b59b-94aaecec062b
-- title:
--   Ad Lat: adele neg integral
-- statement:
--   The Ad Lat construction uses the adele neg integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/AdelicCompletionFractionalIdealProperties.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/AdelicCompletionFractionalIdealProperties.lean#L25-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem GlobalTheory.AdLat.adele_neg_integral {a : FiniteAdeleRing (𝓞 F) F} {v : HeightOneSpectrum (𝓞 F)}
    (ha : a v ∈ v.adicCompletionIntegers F) :
    (-a) v ∈ v.adicCompletionIntegers F := by sorry
