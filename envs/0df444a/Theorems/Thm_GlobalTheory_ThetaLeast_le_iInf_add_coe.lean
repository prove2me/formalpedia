-- Prove2me | Theorems.Thm_GlobalTheory_ThetaLeast_le_iInf_add_coe
-- name    : GlobalTheory.ThetaLeast.le_iInf_add_coe
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:42:02.757309+00:00
-- url     : https://prove2.me/theorems/0a3ae04d-5b99-5e4f-ae7c-972776295797
-- title:
--   Theta Least: le i Inf add coe
-- statement:
--   The Theta Least construction uses the le i Inf add coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsCombinationIntegers.lean#L171-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsCombinationIntegers.lean#L171-L175

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NabValNMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsIntegralCombinationOfMemHaO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_VVAlgebraMapNonnegDvr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsCombinationIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
open GlobalTheory GlobalTheory.ThetaLeast

theorem GlobalTheory.ThetaLeast.le_iInf_add_coe {ι : Sort*} {X : EReal} {g : ι → EReal} {δ : ℝ} (h : ∀ i, X ≤ g i + (δ : EReal)) :
    X ≤ (⨅ i, g i) + (δ : EReal) := by sorry
