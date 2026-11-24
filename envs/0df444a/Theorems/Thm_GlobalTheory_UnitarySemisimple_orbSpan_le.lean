-- Prove2me | Theorems.Thm_GlobalTheory_UnitarySemisimple_orbSpan_le
-- name    : GlobalTheory.UnitarySemisimple.orbSpan_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:45:28.641686+00:00
-- url     : https://prove2.me/theorems/89ea4a46-1e04-4038-b585-448624cb7079
-- title:
--   Unitary Semisimple: orb Span le
-- statement:
--   The Unitary Semisimple construction uses the orb Span le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIrreducibleSubrepFixedOfUnitary.lean#L111-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIrreducibleSubrepFixedOfUnitary.lean#L111-L113

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsOrthogonalProjectionFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIrreducibleSubrepFixedOfUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnitarySemisimple
variable {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W]

theorem GlobalTheory.UnitarySemisimple.orbSpan_le (ρ : Representation ℂ H W) (y : W) (Z : Subrepresentation ρ)
    (hy : y ∈ Z.toSubmodule) : (orbSpan ρ y).toSubmodule ≤ Z.toSubmodule := by sorry
