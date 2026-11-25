-- Prove2me | Theorems.Thm_GlobalTheory_CuspRep_Irr_ofChar_inj
-- name    : GlobalTheory.CuspRep.Irr.ofChar_inj
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:03:32.151798+00:00
-- url     : https://prove2.me/theorems/cca45909-de9e-571e-876f-b7435eed322a
-- title:
--   Irr: of Char inj
-- statement:
--   The Irr construction uses the of Char inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsIrreducibleIff.lean#L92-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsIrreducibleIff.lean#L92-L100

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsIrreducibleIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Topology
open GlobalTheory GlobalTheory.CuspRep
variable {G : Type} [Group G]
variable [TopologicalSpace G]
attribute [instance] SmIrr.acg SmIrr.mod
variable [IsTopologicalGroup G]

theorem GlobalTheory.CuspRep.Irr.ofChar_inj {χ χ' : G →* ℂˣ} {hχ : IsOpen {g | χ g = 1}} {hχ' : IsOpen {g | χ' g = 1}}
    (h : Irr.ofChar χ hχ = Irr.ofChar χ' hχ') : χ = χ' := by sorry
