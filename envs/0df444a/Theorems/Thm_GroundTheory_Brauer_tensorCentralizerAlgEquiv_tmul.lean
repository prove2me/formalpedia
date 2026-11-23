-- Prove2me | Theorems.Thm_GroundTheory_Brauer_tensorCentralizerAlgEquiv_tmul
-- name    : GroundTheory.Brauer.tensorCentralizerAlgEquiv_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:04:08.774694+00:00
-- url     : https://prove2.me/theorems/88e2fd51-b654-48fb-9449-e7b327da4c49
-- title:
--   Brauer: tensor Centralizer Alg Equiv tmul
-- statement:
--   The Brauer construction uses the tensor Centralizer Alg Equiv tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/DoubleCentralizer.lean#L201-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/DoubleCentralizer.lean#L201-L204

import Mathlib
import Definitions.Def_GroundTheory_Brauer_TensorSimple
import Definitions.Def_GroundTheory_Brauer_SkolemNoether
import Definitions.Def_GroundTheory_Brauer_DoubleCentralizer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Brauer
open TensorProduct Module
open SkolemNoether
variable {K A : Type*} [Field K] [Ring A] [Algebra K A] (B : Subalgebra K A)
open CentralizerModule
variable [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A] [IsSimpleRing B]
variable [Algebra.IsCentral K B]

theorem GroundTheory.Brauer.tensorCentralizerAlgEquiv_tmul (b : B) (c : Subalgebra.centralizer K (B : Set A)) :
    tensorCentralizerAlgEquiv B (b ⊗ₜ[K] c) = (b : A) * c := by sorry
