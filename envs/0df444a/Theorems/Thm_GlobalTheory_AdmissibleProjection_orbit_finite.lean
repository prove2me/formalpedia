-- Prove2me | Theorems.Thm_GlobalTheory_AdmissibleProjection_orbit_finite
-- name    : GlobalTheory.AdmissibleProjection.orbit_finite
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:55:18.793627+00:00
-- url     : https://prove2.me/theorems/ba298bbc-7c0c-4784-98c7-6fccb4292e58
-- title:
--   Admissible Projection: orbit finite
-- statement:
--   The Admissible Projection construction uses the orbit finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIrreducibleEquivariantProjection.lean#L22-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIrreducibleEquivariantProjection.lean#L22-L42

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIrreducibleSubrepFixedOfUnitary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIrreducibleEquivariantProjection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AdmissibleProjection
open GlobalTheory.UnitarySemisimple
variable {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W]

theorem GlobalTheory.AdmissibleProjection.orbit_finite [TopologicalSpace H] [IsTopologicalGroup H] (ρ : Representation ℂ H W)
    (hsm : ∀ w, IsOpen {k : H | ρ k w = w}) (K : Subgroup H) (hK : IsCompact (K : Set H))
    (w : W) : (Set.range fun k : K => ρ k w).Finite := by sorry
