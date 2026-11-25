-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_infComp_vecMul
-- name    : GroundTheory.Automorphic.Reduction.infComp_vecMul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:10:55.907309+00:00
-- url     : https://prove2.me/theorems/f1d571d9-f89e-4216-a08d-417c6448cd39
-- title:
--   Reduction: inf Comp vec Mul
-- statement:
--   The Reduction construction uses the inf Comp vec Mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L88-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L88-L93

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicGLn
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
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
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem GroundTheory.Automorphic.Reduction.infComp_vecMul (w : InfinitePlace K) (y : Fin n → 𝔸[K]) (M : Matrix (Fin n) (Fin n) 𝔸[K]) :
    infComp w (y ᵥ* M) = infComp w y ᵥ* (M.map (infEval w)) := by sorry
