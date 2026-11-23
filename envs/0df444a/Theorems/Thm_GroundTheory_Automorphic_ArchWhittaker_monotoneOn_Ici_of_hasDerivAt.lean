-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ArchWhittaker_monotoneOn_Ici_of_hasDerivAt
-- name    : GroundTheory.Automorphic.ArchWhittaker.monotoneOn_Ici_of_hasDerivAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:08.567682+00:00
-- url     : https://prove2.me/theorems/ba5fe0fb-6de7-46cc-9f96-a744a6f8835a
-- title:
--   Arch Whittaker: monotone On Ici of has Deriv At
-- statement:
--   The Arch Whittaker construction uses the monotone On Ici of has Deriv At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ArchimedeanWhittaker/WronskianEqZeroOfModerate.lean#L36-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ArchimedeanWhittaker/WronskianEqZeroOfModerate.lean#L36-L43

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ArchimedeanWhittaker_WronskianEqZeroOfModerate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ArchWhittaker
open Filter Topology Set

theorem GroundTheory.Automorphic.ArchWhittaker.monotoneOn_Ici_of_hasDerivAt {u u' : ℝ → ℝ} {a : ℝ}
    (hu : ∀ y ≥ a, HasDerivAt u (u' y) y) (hpos : ∀ y ≥ a, 0 ≤ u' y) : MonotoneOn u (Ici a) := by sorry
