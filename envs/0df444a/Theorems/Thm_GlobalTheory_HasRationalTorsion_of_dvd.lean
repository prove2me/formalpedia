-- Prove2me | Theorems.Thm_GlobalTheory_HasRationalTorsion_of_dvd
-- name    : GlobalTheory.HasRationalTorsion.of_dvd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:04:45.699011+00:00
-- url     : https://prove2.me/theorems/d22bd47a-2bbd-4d6d-9650-e8718f0fd737
-- title:
--   Has Rational Torsion: of dvd
-- statement:
--   The Has Rational Torsion construction uses the of dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasRationalTorsionIffMemRange.lean#L27-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasRationalTorsionIffMemRange.lean#L27-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsLineOfAddAddEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasRationalTorsionIffMemRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WeierstrassCurve WeierstrassCurve.Affine Polynomial
variable {K : Type*} [Field K]
variable {W : WeierstrassCurve K} {L : Type*} [Field L] [Algebra K L] {m n : ℕ}

theorem GlobalTheory.HasRationalTorsion.of_dvd (h : HasRationalTorsion W L n) (hmn : m ∣ n) :
    HasRationalTorsion W L m := by sorry
