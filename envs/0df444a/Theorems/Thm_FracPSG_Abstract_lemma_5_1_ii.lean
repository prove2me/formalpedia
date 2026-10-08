-- Prove2me | Theorems.Thm_FracPSG_Abstract_lemma_5_1_ii
-- name    : FracPSG.Abstract.lemma_5_1_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:09:33.481178+00:00
-- url     : https://prove2.me/theorems/6afc7707-73f3-4039-a173-c76194648d5f
-- title:
--   Lemma 5.1(ii) — square-summability of Δₙ
-- statement:
--   In the setting of §5, suppose (H1) and (H3) hold and $h(z_0)<+\infty$. Let $a>0$ satisfy $a\le\alpha_n$ for all $n$ (for instance $a=\underline\alpha:=\inf_n\alpha_n$). Then for every $\bar z\in\Omega_0$,
--   $$\sum_{n=0}^{+\infty}\Delta_n^2\le\frac{h(z_0)-h(\bar z)}{a}<+\infty,$$
--   and consequently $\Delta_n\to0$.
--
--   This is the first quantitative consequence of sufficient decrease; it is used to pass to the limit in the finite-length estimate (24).
--
--   **Formalization Note** The hypothesis $h(z_0)<+\infty$ is implicit on the page (the bound "$<+\infty$" presupposes it) and is made explicit. Stating the bound for every lower bound $a$ of $(\alpha_n)$ is equivalent to stating it for $\underline\alpha$. $h(z_0)$ and $h(\bar z)$ are finite here and enter through `EReal.toReal`; summability is stated explicitly.
-- source:
--   Boţ, Dao, Li, Extrapolated Proximal Subgradient Algorithms for Nonconvex and Nonsmooth Fractional Programs, arXiv:2003.04124v2, p. 14, Lemma 5.1(ii)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty
import Definitions.Def_FracPSG_Abstract_Basic

open Filter Topology

namespace FracPSG.Abstract

open NonconvexSplitting.Shared NonconvexSplitting.ADMMKL

/-- Lemma 5.1(ii) (Boţ–Dao–Li, arXiv:2003.04124v2, p. 14): under (H1) and (H3), with `h(z₀) < +∞`,
if `a > 0` bounds every `αₙ` from below (e.g. `a = α̲ = inf αₙ`), then for every `z̄ ∈ Ω₀`,
`∑_{n ≥ 0} Δₙ² ≤ (h(z₀) - h(z̄))/a < +∞`, and `Δₙ → 0`. -/
theorem lemma_5_1_ii {P : ℕ} {h : EuclideanSpace ℝ (Fin P) → EReal}
    {z : ℕ → EuclideanSpace ℝ (Fin P)} {α β ε : ℕ → ℝ} {Δ : ℤ → ℝ} {ilo ihi : ℤ}
    {lam : ℤ → ℝ}
    (hset : AbstractSetting h α β ε Δ ilo ihi lam)
    (hH1 : H1 h z α Δ) (hH3 : H3 h z) (hz₀ : h (z 0) ≠ ⊤)
    {a : ℝ} (ha : 0 < a) (hαa : ∀ n, a ≤ α n) :
    ∀ zbar ∈ omega0 h z,
      Summable (fun n : ℕ => Δ n ^ 2) ∧
      ∑' n : ℕ, Δ n ^ 2 ≤ ((h (z 0)).toReal - (h zbar).toReal) / a ∧
      Tendsto (fun n : ℕ => Δ n) atTop (𝓝 0) := by sorry

end FracPSG.Abstract
