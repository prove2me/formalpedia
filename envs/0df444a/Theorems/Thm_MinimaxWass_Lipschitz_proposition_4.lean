-- Prove2me | Theorems.Thm_MinimaxWass_Lipschitz_proposition_4
-- name    : MinimaxWass.Lipschitz.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:09:45.523598+00:00
-- url     : https://prove2.me/theorems/adfef906-e4c6-49f0-be6b-0b2df9099ffa
-- title:
--   Proposition 4 (8), p. 4 — Gao–Kleywegt strong duality R_{ϱ,p}(Q, f) = min_{λ≥0} {λϱ^p + E_Q[φ_{λ,f}(Z)]} (bounded case)
-- statement:
--   Let $\mathcal Z$ be a bounded Polish space with metric $d_{\mathcal Z}$, let $p \ge 1$ and $\varrho > 0$, let $f : \mathcal Z \to \mathbb R$ be upper semicontinuous with $0 \le f \le M$, and let $Q$ be a Borel probability measure on $\mathcal Z$. With $\varphi_{\lambda,f}(z) = \sup_{z'}\{f(z') - \lambda d^p_{\mathcal Z}(z,z')\}$, the local worst-case risk equals the value of a one-dimensional dual problem, and the dual minimum is attained:
--
--   $$R_{\varrho,p}(Q,f) = \min_{\lambda \ge 0}\big\{\lambda\varrho^p + \mathbf E_Q[\varphi_{\lambda,f}(Z)]\big\}.$$
--
--   Concretely: $R_{\varrho,p}(Q,f) \le \lambda\varrho^p + \mathbf E_Q[\varphi_{\lambda,f}]$ for every $\lambda \ge 0$, and equality holds for some $\lambda \ge 0$.
--
--   This duality converts a supremum over a Wasserstein ball of measures into a minimization over one real multiplier; every step of the proof of Theorem 2 that compares $R_{\varrho,p}(P,\cdot)$ with $R_{\varrho,p}(P_n,\cdot)$ goes through it.
--
--   **Formalization Note** The paper states Proposition 4 for every upper semicontinuous $f$ and every $Q \in \mathcal P_p(\mathcal Z)$, citing Gao and Kleywegt. This item is the bounded case used throughout §3: $\mathcal Z$ bounded (Assumption 1), $0 \le f \le M$ (Assumption 2), and $\varrho > 0$ (the paper's standing choice; at $\varrho = 0$ the minimum can fail to be attained). "min" is read as attained.
-- source:
--   Lee & Raginsky, Minimax statistical learning with Wasserstein distances, arXiv:1705.07815v2, p. 4, Proposition 4, display (8)

import Mathlib
import Definitions.Def_MinimaxWass_Lipschitz_Setting

open MeasureTheory WassersteinLinOpt.Ball
open scoped ENNReal NNReal

namespace MinimaxWass.Lipschitz

theorem proposition_4 {𝒵 : Type*} [MetricSpace 𝒵] [MeasurableSpace 𝒵] [BorelSpace 𝒵]
    [PolishSpace 𝒵] (hZ : Bornology.IsBounded (Set.univ : Set 𝒵))
    {p ϱ M : ℝ} (hp : 1 ≤ p) (hϱ : 0 < ϱ)
    (f : 𝒵 → ℝ) (hf_usc : UpperSemicontinuous f) (hf_bdd : ∀ z, 0 ≤ f z ∧ f z ≤ M)
    (Q : ProbabilityMeasure 𝒵) :
    (∀ lam : ℝ, 0 ≤ lam →
        MinimaxWass.DataDep.localRisk p ϱ Q f ≤ lam * ϱ ^ p + ∫ z, MinimaxWass.DataDep.phi p lam f z ∂(Q : Measure 𝒵)) ∧
      ∃ lam : ℝ, 0 ≤ lam ∧
        MinimaxWass.DataDep.localRisk p ϱ Q f = lam * ϱ ^ p + ∫ z, MinimaxWass.DataDep.phi p lam f z ∂(Q : Measure 𝒵) := by sorry

end MinimaxWass.Lipschitz
