-- Prove2me | Theorems.Thm_GlobalTheory_CubeColim_termMap_comp
-- name    : GlobalTheory.CubeColim.termMap_comp
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:27:59.177027+00:00
-- url     : https://prove2.me/theorems/567d9971-f8cc-49d0-b1dc-7166f1fad2d3
-- title:
--   Cube Colim: term Map comp
-- statement:
--   The Cube Colim construction uses the term Map comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CechComplexDirectLimit.lean#L12-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CechComplexDirectLimit.lean#L12-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechComplexDirectLimit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits Filter
open GlobalTheory
open GlobalTheory.CubeColim
variable {ι : Type} [LinearOrder ι] [Fintype ι]

theorem GlobalTheory.CubeColim.termMap_comp {X Y Z : Cube.{0} ι ℤ} (f : X ⟶ Y) (g : Y ⟶ Z) (p : ℕ)
    (x : Cube.Term X p) :
    Cube.termMap (f ≫ g) p x = Cube.termMap g p (Cube.termMap f p x) := by sorry
