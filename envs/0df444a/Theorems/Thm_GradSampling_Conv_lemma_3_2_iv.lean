-- Prove2me | Theorems.Thm_GradSampling_Conv_lemma_3_2_iv
-- name    : GradSampling.Conv.lemma_3_2_iv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:48:23.202284+00:00
-- url     : https://prove2.me/theorems/55b6a445-eb47-4f93-9dfa-4d4413707589
-- title:
--   Lemma 3.2(iv), p. 759 — ρ_ε is upper semicontinuous
-- statement:
--   Let $D\subseteq\mathbb R^n$ be open and dense, $f$ continuously differentiable on $D$, and $\epsilon>0$. Then the function $\rho_\epsilon(x)=\operatorname{dist}(0\mid G_\epsilon(x))$ is upper semicontinuous on $\mathbb R^n$:
--
--   $$\limsup_{x\to\bar x}\rho_\epsilon(x)\le\rho_\epsilon(\bar x)\qquad\text{for every }\bar x\in\mathbb R^n.$$
--
--   In the convergence proof this makes the set $\{x\in\mathcal L:\rho_\epsilon(x)\ge\eta\}$ closed, hence compact.
--
--   **Formalization Note** The paper states Lemma 3.2 under the preamble hypothesis $0<\rho_\epsilon(\bar x)$ (and with $m$, $\delta$). Part (iv) is stated here at every $\bar x$: the proof of Theorem 3.4 needs upper semicontinuity at every limit point of $\{x\in\mathcal L:\rho_\epsilon(x)\ge\eta\}$, and the argument for (i), from which (iv) follows, does not use $\rho_\epsilon(\bar x)>0$.
-- source:
--   Burke, Lewis, Overton, A robust gradient sampling algorithm for nonsmooth, nonconvex optimization, SIAM J. Optim. 15 (2005), p. 759, Lemma 3.2(iv) (preamble on p. 758)

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_GradSampling_Conv_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace GradSampling.Conv

/-- Lemma 3.2(iv), p. 759: `ρ_ε` is upper semicontinuous on `ℝⁿ`. -/
theorem lemma_3_2_iv {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (D : Set (EuclideanSpace ℝ (Fin n)))
    (hDo : IsOpen D) (hDd : Dense D) (hC1 : ContDiffOn ℝ 1 f D) (ε : ℝ) (hε : 0 < ε) :
    UpperSemicontinuous (rho f D ε) := by sorry

end GradSampling.Conv
