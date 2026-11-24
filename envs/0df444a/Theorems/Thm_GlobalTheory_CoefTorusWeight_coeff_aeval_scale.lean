-- Prove2me | Theorems.Thm_GlobalTheory_CoefTorusWeight_coeff_aeval_scale
-- name    : GlobalTheory.CoefTorusWeight.coeff_aeval_scale
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:15:54.621093+00:00
-- url     : https://prove2.me/theorems/02d52b99-a0ae-4b40-8e69-dbb548b95d65
-- title:
--   Coef Torus Weight: coeff aeval scale
-- statement:
--   The Coef Torus Weight construction uses the coeff aeval scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeylTensorCoefSpaceEndomorphismPreservesTorusWei.lean#L12-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeylTensorCoefSpaceEndomorphismPreservesTorusWei.lean#L12-L28

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeylTensorCoefSpaceEndomorphismPreservesTorusWei
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix
open GlobalTheory GlobalTheory.CoefTorusWeight

theorem GlobalTheory.CoefTorusWeight.coeff_aeval_scale {K σ : Type} [Field K] [Fintype σ] (c : σ → K) (F : MvPolynomial σ K)
    (m : σ →₀ ℕ) :
    coeff m (aeval (fun v => (C (c v) * X v : MvPolynomial σ K)) F) = (∏ v, c v ^ m v) * coeff m F := by sorry
