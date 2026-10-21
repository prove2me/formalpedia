-- Prove2me | Theorems.Thm_NaiveLearn_OverMatch_lemma_4
-- name    : NaiveLearn.OverMatch.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:17:22.118345+00:00
-- url     : https://prove2.me/theorems/36fe9cb5-c25e-4eb8-ab00-08b44db45c33
-- title:
--   Lemma 4, p. 22 — for small δ the solution of (10) converges to 1 if ⟨µ^W, x¹⟩ > p + η and to 0 if ⟨µ^W, x¹⟩ < p − η
-- statement:
--   Let $0<p<1$, let $(\sigma_\delta)_{\delta\in(0,1]}$ be an extremization family for the prior $p$, and let $W$ be the weight matrix of a strongly connected network (row-stochastic, irreducible, $w_{ii}>0$) with centrality measure $\mu^W$. For $\mathbf x^1\in[0,1]^m$ let $z^\delta$ solve (10),
--   $$
--   \dot z^\delta=W\vec\sigma_\delta(z^\delta)-z^\delta,\qquad z^\delta(0)=\mathbf x^1,\qquad \vec\sigma_\delta(z)=(\sigma_\delta(z_1),\dots,\sigma_\delta(z_m)).
--   $$
--   Then for every $\eta>0$ there is $\delta_0\in(0,1]$ such that for every $\delta\in(0,\delta_0]$ and every $\mathbf x^1\in[0,1]^m$:
--
--   1. if $\langle\mu^W,\mathbf x^1\rangle>p+\eta$ then $\lim_{t\to\infty}z^\delta(t)=\mathbf 1$;
--   2. if $\langle\mu^W,\mathbf x^1\rangle<p-\eta$ then $\lim_{t\to\infty}z^\delta(t)=\mathbf 0$.
--
--   The extremization dynamics thus first approach the DeGroot consensus and are then driven to the corner on the side of $p$ where the consensus lies.
--
--   **Formalization Note** The page says "there exists $\delta>0$"; its proof produces a threshold $\delta_0$ that works for every $\delta<\delta_0$ and every $\mathbf x^1\in X$ (compactness of $X$), which is how Lemma 6 uses it ("for all sufficiently small $\delta>0$"). The statement is posed in that form. Property 3 of an extremization rule is taken uniform in $x$, as the proof uses.
-- source:
--   Arieli, Babichenko & Mueller-Frank, Naive Learning Through Probability Over-Matching, SSRN working paper 3338015 (version of August 3, 2020), p. 22, Lemma 4, (10)

import Mathlib
import Definitions.Def_NaiveLearn_OverMatch_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace NaiveLearn.OverMatch

/-- Lemma 4, p. 22: for every `η > 0` there is `δ₀ ∈ (0, 1]` such that for every `δ ∈ (0, δ₀]` and
every `x¹ ∈ [0, 1]^m`, the solution of (10), `ż = W σ⃗_δ(z) − z`, `z(0) = x¹`, converges to `1` if
`⟨µ^W, x¹⟩ > p + η` and to `0` if `⟨µ^W, x¹⟩ < p − η`. -/
theorem lemma_4 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (σ : ℝ → ℝ → ℝ)
    (hσ : IsExtremizationFamily p σ) {m : ℕ} (W : Matrix (Fin m) (Fin m) ℝ) (μ : Fin m → ℝ)
    (hW : IsWeightMatrix W) (hμ : IsCentrality W μ) :
    ∀ η : ℝ, 0 < η → ∃ δ0 ∈ Set.Ioc (0 : ℝ) 1, ∀ δ ∈ Set.Ioc (0 : ℝ) δ0,
      ∀ x1 : Fin m → ℝ, (∀ i, x1 i ∈ Set.Icc (0 : ℝ) 1) →
      ∀ z : ℝ → (Fin m → ℝ), IsODESolution (meanField (σ δ) W) z → z 0 = x1 →
        (p + η < ∑ i, μ i * x1 i → Tendsto z atTop (𝓝 1)) ∧
        (∑ i, μ i * x1 i < p - η → Tendsto z atTop (𝓝 0)) := by sorry

end NaiveLearn.OverMatch
