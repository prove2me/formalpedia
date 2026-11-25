-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ArchWhittaker_antitoneOn_Ici_of_hasDerivAt
-- name    : GroundTheory.Automorphic.ArchWhittaker.antitoneOn_Ici_of_hasDerivAt
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:29:12.89626+00:00
-- url     : https://prove2.me/theorems/d666a6f6-a967-440f-b724-580fa2d7f881
-- title:
--   Arch Whittaker: antitone On Ici of has Deriv At
-- statement:
--   The Arch Whittaker construction uses the antitone On Ici of has Deriv At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ArchimedeanWhittaker/WronskianEqZeroOfModerate.lean#L45-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ArchimedeanWhittaker/WronskianEqZeroOfModerate.lean#L45-L51

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

theorem GroundTheory.Automorphic.ArchWhittaker.antitoneOn_Ici_of_hasDerivAt {u u' : ℝ → ℝ} {a : ℝ}
    (hu : ∀ y ≥ a, HasDerivAt u (u' y) y) (hneg : ∀ y ≥ a, u' y ≤ 0) : AntitoneOn u (Ici a) := by sorry
