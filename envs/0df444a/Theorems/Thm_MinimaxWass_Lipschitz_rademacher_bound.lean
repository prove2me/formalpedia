-- Prove2me | Theorems.Thm_MinimaxWass_Lipschitz_rademacher_bound
-- name    : MinimaxWass.Lipschitz.rademacher_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:09:59.812964+00:00
-- url     : https://prove2.me/theorems/57b60570-af00-4815-9bee-ead8fc9f18ae
-- title:
--   Appendix C.3, p. 15 — ℜ_n(Φ) ≤ (24/√n)𝔆(ℱ) + 24L·diam(𝒵)^p/(√n ϱ^{p−1}) for Φ built on Λ = [0, Lϱ^{−(p−1)}] (stray C₀ dropped)
-- statement:
--   Let $\mathcal Z$ be a bounded Polish space with diameter $\operatorname{diam}(\mathcal Z)$, $p \ge 1$, $\varrho > 0$, and $\mathcal F$ a class of upper semicontinuous functions with $0 \le f \le M$ that are uniformly $L$-Lipschitz with $L \ge 0$ (Assumptions 1–3), with finite entropy integral $\mathfrak C(\mathcal F)$. Let $Z_1,\dots,Z_n$ ($n \ge 1$) be i.i.d. from a probability measure $P$, and let $\Phi = \{\varphi_{\lambda,f} : \lambda \in [0, L\varrho^{-(p-1)}],\ f \in \mathcal F\}$. Then the expected Rademacher average of $\Phi$ satisfies
--
--   $$\mathfrak R_n(\Phi) \le \frac{24}{\sqrt n}\,\mathfrak C(\mathcal F) + \frac{24 L\cdot\operatorname{diam}(\mathcal Z)^p}{\sqrt n\,\varrho^{p-1}}.$$
--
--   This is the complexity estimate that, combined with (C.4) and (C.5), yields the constants $48$ and $48L$ of Theorem 2. It is the analogue of Lemma 5 (Appendix D) for the interval $\Lambda$ of Lemma 1.
--
--   **Formalization Note** The printed bound carries a factor $C_0$ (the constant of Assumption 4) in its second term. Assumption 4 is not among the hypotheses of Theorem 2, and Lemma 5's computation with $|\Lambda| = L\varrho^{-(p-1)}$ gives exactly the bound above, which is also what the $48L$ term of (10) requires; the stray $C_0$ is dropped. $\mathfrak C(\mathcal F) < \infty$ is a disclosed pin (the bound is vacuous otherwise, and it makes the supremum measurable); $\mathfrak C(\mathcal F)$ enters as a real number. The covering number is the internal one. $L \ge 0$ is a disclosed pin.
-- source:
--   Lee & Raginsky, Minimax statistical learning with Wasserstein distances, arXiv:1705.07815v2, p. 15, Appendix C.3 (bound on ℜ_n(Φ)); cf. Lemma 5 and its proof, Appendix D, pp. 19–20

import Mathlib
import Definitions.Def_MinimaxWass_Lipschitz_Setting

open MeasureTheory WassersteinLinOpt.Ball
open scoped ENNReal NNReal

namespace MinimaxWass.Lipschitz

theorem rademacher_bound {𝒵 : Type*} [MetricSpace 𝒵] [MeasurableSpace 𝒵] [BorelSpace 𝒵]
    [PolishSpace 𝒵] (hZ : Bornology.IsBounded (Set.univ : Set 𝒵))
    {p ϱ M L : ℝ} (hp : 1 ≤ p) (hϱ : 0 < ϱ)
    (ℱ : Set (𝒵 → ℝ)) (hF_usc : ∀ f ∈ ℱ, UpperSemicontinuous f)
    (hF_bdd : ∀ f ∈ ℱ, ∀ z, 0 ≤ f z ∧ f z ≤ M)
    (hL : 0 ≤ L) (hF_lip : ∀ f ∈ ℱ, ∀ z z' : 𝒵, f z' - f z ≤ L * dist z' z)
    (hC : MinimaxWass.DataDep.entropyIntegral ℱ < ⊤)
    (P : ProbabilityMeasure 𝒵) {n : ℕ} (hn : 0 < n) :
    rademacherAvg P n (phiClass p ϱ L ℱ) ≤
      24 / Real.sqrt n * (MinimaxWass.DataDep.entropyIntegral ℱ).toReal +
        24 * L * Metric.diam (Set.univ : Set 𝒵) ^ p / (Real.sqrt n * ϱ ^ (p - 1)) := by sorry

end MinimaxWass.Lipschitz
