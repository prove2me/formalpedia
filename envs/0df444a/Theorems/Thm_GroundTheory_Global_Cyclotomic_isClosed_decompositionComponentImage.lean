-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_isClosed_decompositionComponentImage
-- name    : GroundTheory.Global.Cyclotomic.isClosed_decompositionComponentImage
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:13:43.167367+00:00
-- url     : https://prove2.me/theorems/f315cc85-eb32-4f30-9eb0-8cad90d127e5
-- title:
--   Cyclotomic: is Closed decomposition Component Image
-- statement:
--   The Cyclotomic construction uses the is Closed decomposition Component Image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/DegreeDecomposition.lean#L283-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/DegreeDecomposition.lean#L283-L286

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
variable (q : Nat.Primes) (P : Ideal (𝓞 ℚ̄))

theorem GroundTheory.Global.Cyclotomic.isClosed_decompositionComponentImage :
    IsClosed (decompositionComponentImage q P : Set ℤ_[q]) := by sorry
