-- Prove2me | Theorems.Thm_GlobalTheory_SatBlocks_ne_zero_of_val_zero
-- name    : GlobalTheory.SatBlocks.ne_zero_of_val_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:14:50.648043+00:00
-- url     : https://prove2.me/theorems/06ee2db4-e3c2-4652-8025-32a6385e075e
-- title:
--   Sat Blocks: ne zero of val zero
-- statement:
--   The Sat Blocks construction uses the ne zero of val zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/SaturatedBlocksSummand.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/SaturatedBlocksSummand.lean#L28-L31

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_SaturatedBlocksSummand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
open GlobalTheory GlobalTheory.SatBlocks

theorem GlobalTheory.SatBlocks.ne_zero_of_val_zero {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {z : C}
    (h : v z = 0) : z ≠ 0 := by sorry
