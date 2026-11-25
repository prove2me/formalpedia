-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_exists_degreeComponent_ne_one
-- name    : GroundTheory.Global.Cyclotomic.exists_degreeComponent_ne_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:13:49.030865+00:00
-- url     : https://prove2.me/theorems/28e43d36-c4d0-4768-810a-d54b96a1c971
-- title:
--   Cyclotomic: exists degree Component ne one
-- statement:
--   The Cyclotomic construction uses the exists degree Component ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/DegreeDecomposition.lean#L172-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/DegreeDecomposition.lean#L172-L187

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Degree
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ClosedSubgroups
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_DegreeDecomposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Filter Topology
open scoped GroundTheory.LocalField.Abstract Pointwise
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
open GroundTheory.LocalField.Abstract
local notation "ℚ̄" => AlgebraicClosure ℚ

theorem GroundTheory.Global.Cyclotomic.exists_degreeComponent_ne_one (q : Nat.Primes) (w : ℤ_[q]ˣ)
    (hw : padicUnitsLog q w ≠ 1) :
    ∃ N, 0 < N ∧ ∀ σ : Gal(ℚ̄/ℚ), (modCharacter ((q : ℕ) ^ N) σ : ZMod ((q : ℕ) ^ N)) =
      PadicInt.toZModPow N (w : ℤ_[q]) → degreeComponent q σ ≠ 1 := by sorry
