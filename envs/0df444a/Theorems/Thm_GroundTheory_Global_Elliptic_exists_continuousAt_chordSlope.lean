-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_exists_continuousAt_chordSlope
-- name    : GroundTheory.Global.Elliptic.exists_continuousAt_chordSlope
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T06:14:47.983798+00:00
-- url     : https://prove2.me/theorems/ac9462b1-2ee6-4000-bd2d-21b7155f80bf
-- title:
--   Elliptic: exists continuous At chord Slope
-- statement:
--   The Elliptic construction uses the exists continuous At chord Slope property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/UniformizationAddition.lean#L422-L447
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/UniformizationAddition.lean#L422-L447

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticDegree
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationAddition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
open scoped PeriodPair
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {L : PeriodPair}

theorem GroundTheory.Global.Elliptic.exists_continuousAt_chordSlope {w : ℂ} (hw : w ∉ L.lattice) (h2w : 2 * w ∉ L.lattice) :
    ∃ s : ℂ → ℂ, ContinuousAt s w ∧ s w = tangentSlope L w ∧
      ∀ᶠ z in 𝓝[≠] w, z ∉ L.lattice ∧ z - w ∉ L.lattice ∧ z + w ∉ L.lattice ∧
        chordSlope L z w = s z := by sorry
