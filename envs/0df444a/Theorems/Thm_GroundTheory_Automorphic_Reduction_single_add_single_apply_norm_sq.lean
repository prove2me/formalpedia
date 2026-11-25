-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_single_add_single_apply_norm_sq
-- name    : GroundTheory.Automorphic.Reduction.single_add_single_apply_norm_sq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:07:43.442605+00:00
-- url     : https://prove2.me/theorems/f1d6637a-adc3-5d1f-a321-d8084996e867
-- title:
--   Reduction: single add single apply norm sq
-- statement:
--   The Reduction construction uses the single add single apply norm sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionCore.lean#L29-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionCore.lean#L29-L38

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionFinite
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionBlock
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionDirichlet
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory.Global GroundTheory.Global.IdeleGroup
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K]
variable {E : Type*} [NormedField E] {n : ℕ}

theorem GroundTheory.Automorphic.Reduction.single_add_single_apply_norm_sq {i i' : Fin n} (h : i ≠ i') (x y : E) (k : Fin n) :
    ‖(Pi.single i x + Pi.single i' y : Fin n → E) k‖ ^ 2 =
      (Pi.single i (‖x‖ ^ 2) : Fin n → ℝ) k + (Pi.single i' (‖y‖ ^ 2) : Fin n → ℝ) k := by sorry
