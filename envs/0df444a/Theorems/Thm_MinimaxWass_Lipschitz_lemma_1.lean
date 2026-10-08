-- Prove2me | Theorems.Thm_MinimaxWass_Lipschitz_lemma_1
-- name    : MinimaxWass.Lipschitz.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:09:41.873873+00:00
-- url     : https://prove2.me/theorems/473c179b-b4f1-4a70-af71-ececf33b531a
-- title:
--   Lemma 1, p. 6 — under Assumptions 1–3 the optimal dual multiplier satisfies λ̃ ≤ Lϱ^{−(p−1)}
-- statement:
--   Let $\mathcal Z$ be a bounded Polish space, $p \ge 1$, $\varrho > 0$, and let $\mathcal F$ be a class of upper semicontinuous functions with $0 \le f \le M$ (Assumptions 1–2) that are uniformly $L$-Lipschitz (Assumption 3): for some $L \ge 0$,
--   $$f(z') - f(z) \le L\, d_{\mathcal Z}(z',z) \quad \text{for all } f \in \mathcal F,\ z, z' \in \mathcal Z.$$
--   Fix a probability measure $Q$ on $\mathcal Z$. Let $\tilde f \in \mathcal F$ minimize $R_{\varrho,p}(Q,\cdot)$ over $\mathcal F$, and let $\tilde\lambda \ge 0$ minimize $\lambda \mapsto \lambda\varrho^p + \mathbf E_Q[\varphi_{\lambda,\tilde f}(Z)]$ over $\lambda \ge 0$. Then
--
--   $$\tilde\lambda \le L\varrho^{-(p-1)}.$$
--
--   The lemma confines the dual multiplier of the local minimax problem, for the true and for the empirical distribution alike, to the fixed interval $\Lambda = [0, L\varrho^{-(p-1)}]$; this is what makes the class $\Phi = \{\varphi_{\lambda,f}\}$ used in the proof of Theorem 2 have finite complexity.
--
--   **Formalization Note** $\tilde f$ and $\tilde\lambda$ are given as hypotheses of minimality rather than as `argmin` terms. The constant $L$ is quantified once, before the functions it bounds, and $L \ge 0$ is a disclosed pin: a Lipschitz constant is nonnegative, and the pin matters only on a one-point space, where the printed condition is vacuous. The paper's $Q \in \mathcal P_p(\mathcal Z)$ is automatic on a bounded space.
-- source:
--   Lee & Raginsky, Minimax statistical learning with Wasserstein distances, arXiv:1705.07815v2, p. 6, Lemma 1; Assumption 3 p. 5; proof Appendix C.2, p. 15

import Mathlib
import Definitions.Def_MinimaxWass_Lipschitz_Setting

open MeasureTheory WassersteinLinOpt.Ball
open scoped ENNReal NNReal

namespace MinimaxWass.Lipschitz

theorem lemma_1 {𝒵 : Type*} [MetricSpace 𝒵] [MeasurableSpace 𝒵] [BorelSpace 𝒵]
    [PolishSpace 𝒵] (hZ : Bornology.IsBounded (Set.univ : Set 𝒵))
    {p ϱ M L : ℝ} (hp : 1 ≤ p) (hϱ : 0 < ϱ)
    (ℱ : Set (𝒵 → ℝ)) (hF_usc : ∀ f ∈ ℱ, UpperSemicontinuous f)
    (hF_bdd : ∀ f ∈ ℱ, ∀ z, 0 ≤ f z ∧ f z ≤ M)
    (hL : 0 ≤ L) (hF_lip : ∀ f ∈ ℱ, ∀ z z' : 𝒵, f z' - f z ≤ L * dist z' z)
    (Q : ProbabilityMeasure 𝒵)
    (ftil : 𝒵 → ℝ) (hftil_mem : ftil ∈ ℱ)
    (hftil_min : ∀ f ∈ ℱ, MinimaxWass.DataDep.localRisk p ϱ Q ftil ≤ MinimaxWass.DataDep.localRisk p ϱ Q f)
    (lamtil : ℝ) (hlamtil_nonneg : 0 ≤ lamtil)
    (hlamtil_min : ∀ lam : ℝ, 0 ≤ lam →
      lamtil * ϱ ^ p + ∫ z, MinimaxWass.DataDep.phi p lamtil ftil z ∂(Q : Measure 𝒵) ≤
        lam * ϱ ^ p + ∫ z, MinimaxWass.DataDep.phi p lam ftil z ∂(Q : Measure 𝒵)) :
    lamtil ≤ L * ϱ ^ (-(p - 1)) := by sorry

end MinimaxWass.Lipschitz
