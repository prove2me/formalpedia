-- Prove2me | Theorems.Thm_JacodTodorov10_LLN_eq_8_29
-- name    : JacodTodorov10.LLN.eq_8_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:21:19.599209+00:00
-- url     : https://prove2.me/theorems/80dcb82f-0090-43da-955a-ea2c945345a4
-- title:
--   (8.29) — lim_{m→∞} supₙ E(Hⁿ(m)ₜ) = 0: the small-jump remainder vanishes
-- statement:
--   Assume (H-$r$) with $r<2$, (K-$v$), the localized bound (8.3) with function $\gamma$, and (3.3), and for each $m$ let $X''(m)$ be the small-jump process of (8.5) (jumps $\delta(s,z)$ with $\gamma(z)\le1/m$). Then for every $t$,
--   $$\lim_{m\to\infty}\ \sup_n\ \mathbb E\big(H^n(m)_t\big)=0,\qquad H^n(m)_t=\sum_{i=k_n+1}^{[t/\Delta_n]-k_n}|\Delta^n_iX''(m)|^r\big(1+\widehat c(k_n)_{i-k_n-1}+\widehat c(k_n)_i\big).$$
--
--   In case (c) of Theorem 3.1, $H^n(m)$ dominates (up to a constant) the part of $U(F,k_n)$ not accounted for by the big jumps; (8.29) is what remains to show after (8.27).
--
--   **Formalization Note** The page's $H^n(m)_t$ carries a constant factor $K>0$, dropped here since it does not affect the limit $0$. $|x|^0$ is read as $1_{\{x\ne0\}}$. The expectation is the Lebesgue integral of the nonnegative variable $H^n(m)_t$ in $[0,\infty]$.
-- source:
--   Jacod, Todorov, Do price and volatility jump together?, arXiv:1010.4990v1 (Ann. Appl. Probab. 20 (2010)), §8.4, step 4, (8.29), p. 34; X″(m) from (8.5), p. 26

import Mathlib
import Definitions.Def_JacodTodorov10_LLN_Local

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace JacodTodorov10.LLN

/-- **(8.29)** of Jacod–Todorov, *Do price and volatility jump together?*, arXiv:1010.4990v1
(Ann. Appl. Probab. 20 (2010)), §8.4, step 4, p. 34: assume (H-r) with `r < 2`, (K-v), (8.3) and
(3.3), and let `X''(m)` be the small-jump processes of (8.5). Then for every `t`,
`lim_{m → ∞} sup_n E(H^n(m)_t) = 0`, where
`H^n(m)_t = ∑_{i = k_n+1}^{[t/Δ_n] − k_n} |Δ^n_i X''(m)|^r (1 + ĉ(k_n)_{i−k_n−1} + ĉ(k_n)_i)`.

Formalization Note: the page's `H^n(m)_t` carries a constant factor `K > 0`, which is dropped: it
does not change whether the limit is `0`. `|x|^r` is `pow0`, so at `r = 0` a zero increment
contributes `0` (`|x|^0 = 1_{x ≠ 0}`). The expectation is the lower Lebesgue integral of the
nonnegative variable `H^n(m)_t`, so it is never a junk value. `γ` (in `A_m`) is the function of
(8.3). -/
theorem eq_8_29 {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (lam : Measure E) [SigmaFinite lam] (M : Data Ω E) (r v C : ℝ) (Γ : ℝ≥0 → Ω → ℝ)
    (γ γhat : E → ℝ) (S : Scheme) (ϖ ρ : ℝ)
    (hM : IsModel 𝓕 P lam M) (hH : HAssume 𝓕 P lam r M) (hr : r < 2)
    (hK : KAssume 𝓕 P lam v M) (hB : Bdd83 lam M r v C Γ γ γhat) (hS : S.Cond33 ϖ ρ)
    (Xpp : ℕ → ℝ≥0 → Ω → ℝ) (hXpp : ∀ m, IsXpp P lam M.N M.δ γ r m (Xpp m)) (t : ℝ≥0) :
    Tendsto (fun m => ⨆ n, ∫⁻ ω, ENNReal.ofReal (Hn S M.X (Xpp m) r n t ω) ∂P) atTop (𝓝 0) := by sorry

end JacodTodorov10.LLN
