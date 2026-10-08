-- Prove2me | Theorems.Thm_MinimaxWass_Smooth_proposition_4
-- name    : MinimaxWass.Smooth.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:12:27.472142+00:00
-- url     : https://prove2.me/theorems/a713bb50-bf5c-4964-b961-55c88b506ab4
-- title:
--   Proposition 4, p. 4 — strong duality R_{ϱ,p}(Q,f) = min_{λ≥0} {λϱ^p + E_Q[φ_{λ,f}(Z)]} (8), bounded usc f
-- statement:
--   Let $\mathcal Z$ be a bounded Polish metric space with metric $d_{\mathcal Z}$, let $p\ge1$ and $\varrho>0$, and let $f:\mathcal Z\to\mathbb R$ be upper semicontinuous with $0\le f\le M$. For every Borel probability measure $Q$ on $\mathcal Z$, the local worst-case risk equals the value of a one-dimensional dual problem, and the dual minimum is attained:
--
--   $$R_{\varrho,p}(Q,f)=\min_{\lambda\ge0}\Bigl\{\lambda\varrho^p+\mathbf E_Q[\varphi_{\lambda,f}(Z)]\Bigr\},\qquad \varphi_{\lambda,f}(z)=\sup_{z'\in\mathcal Z}\bigl\{f(z')-\lambda\,d^p_{\mathcal Z}(z,z')\bigr\}.$$
--
--   Concretely: $R_{\varrho,p}(Q,f)\le\lambda\varrho^p+\mathbf E_Q[\varphi_{\lambda,f}(Z)]$ for every $\lambda\ge0$, and equality holds for some $\lambda\ge0$.
--
--   This strong duality result, due to Gao and Kleywegt, converts the supremum over the Wasserstein ball into a minimisation over a single multiplier; every bound in the paper's analysis of the local minimax ERM rests on it.
--
--   **Formalization Note** The paper states Proposition 4 for every upper semicontinuous $f$ and every $Q\in\mathcal P_p(\mathcal Z)$. This item is the bounded case — $\mathcal Z$ bounded (Assumption 1) and $0\le f\le M$ (Assumption 2) — which is the only setting in which the paper uses it; in the general case values can be infinite. $\varrho>0$ is the paper's standing assumption (p. 3); at $\varrho=0$ the minimum can fail to be attained. Under boundedness every $Q$ has finite $p$-th moments, so $Q$ ranges over all Borel probability measures.
-- source:
--   Lee & Raginsky, Minimax statistical learning with Wasserstein distances, arXiv:1705.07815v2, p. 4, Proposition 4, (8) (due to Gao & Kleywegt [11])

import Mathlib
import Definitions.Def_MinimaxWass_Smooth_Setting

open MeasureTheory
open scoped ENNReal NNReal

namespace MinimaxWass.Smooth

/-- Proposition 4 (Gao–Kleywegt strong duality), p. 4, (8), in the bounded setting of §3. -/
theorem proposition_4 {𝒵 : Type*} [MetricSpace 𝒵] [MeasurableSpace 𝒵] [BorelSpace 𝒵] [PolishSpace 𝒵]
    (hbdd : Bornology.IsBounded (Set.univ : Set 𝒵))
    {p ϱ : ℝ} (hp : 1 ≤ p) (hϱ : 0 < ϱ)
    {M : ℝ} (f : 𝒵 → ℝ) (hf_usc : UpperSemicontinuous f) (hf_bdd : ∀ z, 0 ≤ f z ∧ f z ≤ M)
    (Q : ProbabilityMeasure 𝒵) :
    (∀ lam : ℝ, 0 ≤ lam → MinimaxWass.DataDep.localRisk p ϱ Q f ≤ dualObjective p ϱ Q f lam) ∧
      ∃ lam : ℝ, 0 ≤ lam ∧ MinimaxWass.DataDep.localRisk p ϱ Q f = dualObjective p ϱ Q f lam := by sorry

end MinimaxWass.Smooth
