-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_finComp_vecMul
-- name    : GroundTheory.Automorphic.Reduction.finComp_vecMul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:10:02.187392+00:00
-- url     : https://prove2.me/theorems/1e7b8370-3c00-433d-84ab-31c2a1642459
-- title:
--   Reduction: fin Comp vec Mul
-- statement:
--   The Reduction construction uses the fin Comp vec Mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L95-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L95-L101

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

theorem GroundTheory.Automorphic.Reduction.finComp_vecMul (v : HeightOneSpectrum (𝓞 K)) (y : Fin n → 𝔸[K])
    (M : Matrix (Fin n) (Fin n) 𝔸[K]) :
    finComp v (y ᵥ* M) = finComp v y ᵥ* (M.map (finEval v)) := by sorry
