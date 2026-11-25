-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_compactSpace_Ine
-- name    : GlobalTheory.WeilDeligne.compactSpace_Ine
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:10:11.700255+00:00
-- url     : https://prove2.me/theorems/44c8dcd5-ef9c-4e3f-8b9e-ee27ed8e0bd9
-- title:
--   Weil Deligne: compact Space Ine
-- statement:
--   The Weil Deligne construction uses the compact Space Ine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ExistsNotCongPow.lean#L284-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ExistsNotCongPow.lean#L284-L286

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory GlobalTheory.WeilDeligne
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
variable (h : IsPlaceOver A w)
variable {h}
variable [IsAlgClosure E Ω]

theorem GlobalTheory.WeilDeligne.compactSpace_Ine (A : ValuationSubring Ω) : CompactSpace (Ine (F := E) A) := by sorry
