-- Prove2me | Theorems.Thm_MinimaxWass_Lipschitz_display_C4
-- name    : MinimaxWass.Lipschitz.display_C4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:09:58.943328+00:00
-- url     : https://prove2.me/theorems/5271be55-02cc-4387-9327-bf7ad8014a19
-- title:
--   Appendix C.3 with (C.4), pp. 15–17 — w.p. ≥ 1 − δ/2, R_{ϱ,p}(P, f̂) − R_{ϱ,p}(P_n, f̂) ≤ 2ℜ_n(Φ) + M√(2log(2/δ)/n), Λ = [0, Lϱ^{−(p−1)}]
-- statement:
--   Let $\mathcal Z$ be a bounded Polish space, $p \ge 1$, $\varrho > 0$, and $\mathcal F$ a class of upper semicontinuous functions with $0 \le f \le M$ that are uniformly $L$-Lipschitz with $L \ge 0$ (Assumptions 1–3), and with finite entropy integral $\mathfrak C(\mathcal F) < \infty$. Let $Z_1,\dots,Z_n$ ($n \ge 1$) be i.i.d. from $P$, let $\hat f$ be a local minimax ERM (7), and let $0 < \delta < 1$. With $\Lambda = [0, L\varrho^{-(p-1)}]$, $\Phi = \{\varphi_{\lambda,f} : \lambda \in \Lambda, f \in \mathcal F\}$ and $\mathfrak R_n(\Phi)$ the expected Rademacher average of $\Phi$, with probability at least $1 - \delta/2$,
--
--   $$R_{\varrho,p}(P,\hat f) - R_{\varrho,p}(P_n,\hat f) \le 2\,\mathfrak R_n(\Phi) + M\sqrt{\frac{2\log(2/\delta)}{n}}.$$
--
--   This is display (C.4) of the paper's proof of Theorem 3, used with the interval $\Lambda$ of Lemma 1 as Appendix C.3 directs for Theorem 2. It controls the generalization gap of the robust ERM by the complexity of the dual class $\Phi$.
--
--   **Formalization Note** "With probability at least $1-\delta/2$" is stated as: the outer measure under $P^{\otimes n}$ of the set of samples where the inequality fails is at most $\delta/2$ (equal to the probability when that set is measurable, stronger otherwise). The finiteness of $\mathfrak C(\mathcal F)$ is a disclosed pin: it makes $\mathcal F$ totally bounded in the uniform metric, so the suprema over $\Phi$ are measurable and $\mathfrak R_n(\Phi)$ is a genuine expectation. $L \ge 0$ is a disclosed pin, and the ERM is a sample-indexed selection with its minimality hypothesis.
-- source:
--   Lee & Raginsky, Minimax statistical learning with Wasserstein distances, arXiv:1705.07815v2, p. 15, Appendix C.3; pp. 16–17, Appendix C.5, display (C.4) and the definition of ℜ_n(Φ)

import Mathlib
import Definitions.Def_MinimaxWass_Lipschitz_Setting

open MeasureTheory WassersteinLinOpt.Ball
open scoped ENNReal NNReal

namespace MinimaxWass.Lipschitz

theorem display_C4 {𝒵 : Type*} [MetricSpace 𝒵] [MeasurableSpace 𝒵] [BorelSpace 𝒵]
    [PolishSpace 𝒵] (hZ : Bornology.IsBounded (Set.univ : Set 𝒵))
    {p ϱ M L : ℝ} (hp : 1 ≤ p) (hϱ : 0 < ϱ)
    (ℱ : Set (𝒵 → ℝ)) (hF_usc : ∀ f ∈ ℱ, UpperSemicontinuous f)
    (hF_bdd : ∀ f ∈ ℱ, ∀ z, 0 ≤ f z ∧ f z ≤ M)
    (hL : 0 ≤ L) (hF_lip : ∀ f ∈ ℱ, ∀ z z' : 𝒵, f z' - f z ≤ L * dist z' z)
    (hC : MinimaxWass.DataDep.entropyIntegral ℱ < ⊤)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : ProbabilityMeasure 𝒵) {n : ℕ} (hn : 0 < n)
    (fhat : (Fin n → 𝒵) → (𝒵 → ℝ)) (hfhat_mem : ∀ ω, fhat ω ∈ ℱ)
    (hfhat_min : ∀ ω, ∀ f ∈ ℱ,
      MinimaxWass.DataDep.localRisk p ϱ (empiricalPM hn ω) (fhat ω) ≤ MinimaxWass.DataDep.localRisk p ϱ (empiricalPM hn ω) f) :
    Measure.pi (fun _ : Fin n => (P : Measure 𝒵))
        {ω | MinimaxWass.DataDep.localRisk p ϱ P (fhat ω) - MinimaxWass.DataDep.localRisk p ϱ (empiricalPM hn ω) (fhat ω) >
          2 * rademacherAvg P n (phiClass p ϱ L ℱ) +
            M * Real.sqrt (2 * Real.log (2 / δ) / n)} ≤
      ENNReal.ofReal (δ / 2) := by sorry

end MinimaxWass.Lipschitz
