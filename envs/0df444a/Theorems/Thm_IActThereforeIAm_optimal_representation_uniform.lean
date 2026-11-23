-- Prove2me | Theorems.Thm_IActThereforeIAm_optimal_representation_uniform
-- name    : IActThereforeIAm.optimal_representation_uniform
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:07:04.04298+00:00
-- url     : https://prove2.me/theorems/5a32faeb-e48a-4f0b-b8b5-d170ce9853a0
-- title:
--   Theorem 2.1 (additional consequence): for $\lambda>1$ the optimal representation is uniform on $(0,1)^d$
-- statement:
--   Under the hypotheses of Theorem 2.1, but with $\lambda>1$, let $(\mathbf h^\star,\phi^\star)$ be a global minimizer that attains the lower bound $-I(\mathbf s_t;\mathbf s_{t-1},\mathbf a_{t-1})$. Then $H(\mathbf z_t)=0$, and the optimal representation is uniform:
--
--   $$\mathbf z_t=\mathbf h^\star(\mathbf g(\mathbf s_t))\sim\mathrm{Unif}((0,1)^d).$$
-- source:
--   Liu, Huang and Shi, I Act Therefore I Am: When Is JEPA's Action-Conditioning Enough to Learn Causal Mechanisms?, arXiv:2609.31161v1 (2026), Appendix C, last paragraph of the proof of Theorem 2.1, p. 18

import Mathlib
import Definitions.Def_IActThereforeIAm_Basic

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace IActThereforeIAm

theorem optimal_representation_uniform {d : ℕ} {A X Θ : Type*} [MeasurableSpace A]
    [MeasurableSpace X] (M : LatentSCM d A) (hM : M.IsValid) (g : (Fin d → ℝ) → X)
    (hg : Measurable g) (lam : ℝ) (hlam : 1 < lam)
    (model : Θ → (Fin d → ℝ) × A → (Fin d → ℝ) → ℝ)
    (h : X → Fin d → ℝ) (φ : Θ) (hmin : IsGlobalMin M g lam model h φ)
    (hattain : ((objective M g lam h (model φ) : ℝ) : EReal) = -((latentInfo M : ℝ≥0∞) : EReal)) :
    reprLaw M g h = volume.restrict (unitCube d) := by sorry

end IActThereforeIAm
