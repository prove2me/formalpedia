-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_redUnits_character
-- name    : GroundTheory.Global.Cyclotomic.redUnits_character
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:14:05.389855+00:00
-- url     : https://prove2.me/theorems/7dffb007-1faf-45c0-813f-dbefc6f805ed
-- title:
--   Cyclotomic: red Units character
-- statement:
--   The Cyclotomic construction uses the red Units character property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/DegreeDecomposition.lean#L79-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/DegreeDecomposition.lean#L79-L85

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

theorem GroundTheory.Global.Cyclotomic.redUnits_character (q : Nat.Primes) (k : ℕ) (σ : Gal(ℚ̄/ℚ)) :
    (redUnits q k (Units.map (toPadicInt q).toMonoidHom (character σ)) : ZMod ((q : ℕ) ^ k)) =
      (modCharacter ((q : ℕ) ^ k) σ : ZMod ((q : ℕ) ^ k)) := by sorry
