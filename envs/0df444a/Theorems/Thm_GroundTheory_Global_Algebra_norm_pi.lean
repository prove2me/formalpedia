-- Prove2me | Theorems.Thm_GroundTheory_Global_Algebra_norm_pi
-- name    : GroundTheory.Global.Algebra.norm_pi
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:27:39.794833+00:00
-- url     : https://prove2.me/theorems/5e548ab1-8756-4644-8245-d91f0262ed12
-- title:
--   Algebra: norm pi
-- statement:
--   The Algebra construction uses the norm pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/Infinite.lean#L55-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/Infinite.lean#L55-L59

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Infinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.LiesOver TensorProduct
open GroundTheory.Global.Algebra
variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] {A : ι → Type*}
  [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] [∀ i, Module.Free R (A i)]
  [∀ i, Module.Finite R (A i)]

theorem GroundTheory.Global.Algebra.norm_pi (x : ∀ i, A i) : Algebra.norm R x = ∏ i, Algebra.norm R (x i) := by sorry
