-- Prove2me | Theorems.Thm_NumStochOpt_Nonstationary_lemma_p156_conditions_2b_3
-- name    : NumStochOpt.Nonstationary.lemma_p156_conditions_2b_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T19:33:42.901758+00:00
-- url     : https://prove2.me/theorems/141eb33f-cc79-4283-8967-b0217bad3d46
-- title:
--   pp. 155–156 — conditions (2)(b) and (3) of Theorem 6.4 hold for (6.41) with $V(x) = \mathrm{dist}(x, X^*)^2$
-- statement:
--   Assume the hypotheses of Theorem 6.3: $F^0(\cdot, s)$ and $f^0$ are convex continuous functions on $\mathbb R^n$; $X \subseteq \mathbb R^n$ is a nonempty convex compact set; $F^0(\cdot, s) \to f^0$ uniformly on $X$; $g_s$ is a subgradient of $F^0(\cdot, s)$ at $x^s$ with $\|g_s\| \le C$; $x^{s+1} = \pi_X[x^s - \rho_s g_s]$ (6.41); $\rho_s \ge 0$, $\rho_s \to 0$, $\sum_{s=0}^\infty \rho_s = \infty$. Let $X^*$ be the set of minimizers of $f^0$ over $X$ and
--   $$
--   V(x) = \min_{x^* \in X^*} \|x^* - x\|^2 .
--   $$
--   Let $(x^{s_k})$ be a subsequence converging to a point $x' \notin X^*$. Then there is $\varepsilon_0 > 0$ such that for every $\varepsilon \in (0, \varepsilon_0)$:
--
--   1. for every $k$ there is $s \ge s_k$ with $\|x^s - x^{s_k}\| > \varepsilon$, so the exit time $\tau_k = \min\{s \ge s_k : \|x^s - x^{s_k}\| > \varepsilon\}$ is finite;
--   2. $$
--      \limsup_{k \to \infty} V(x^{\tau_k}) < \lim_{k \to \infty} V(x^{s_k}) = V(x').
--      $$
--
--   These are conditions (2)(b) and (3) of Theorem 6.4 for the method (6.41); with the previous milestone they make Theorem 6.4 applicable, which yields Theorem 6.3.
--
--   **Formalization Note** $V(x)$ is the square of `Metric.infDist x X*`. The book derives the quantitative bound $V(x^{\tau_k}) \le V(x^{s_k}) - \varepsilon\delta/(2C)$ and concludes "or equivalently $\overline{\lim}\, V(x^{\tau_k}) < \lim V(x^{s_k})$"; the milestone states that conclusion, in the reading of Theorem 6.4 fixed in its own item. $\rho_s \ge 0$ is added as in Theorem 6.3.
-- source:
--   Yu. Ermoliev, "Stochastic Quasigradient Methods", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 6, pp. 155–156, proof of Theorem 6.3

import Mathlib
import Definitions.Def_NumStochOpt_QuasiFejer_ProjectionMethod
import Definitions.Def_NumStochOpt_Nonstationary_ExitTime

open scoped RealInnerProductSpace
open Filter Topology

namespace NumStochOpt.Nonstationary

/-- Proof of Theorem 6.3, pp. 155–156: under the hypotheses of Theorem 6.3, conditions (2)(b)
and (3) of Theorem 6.4 hold for the iteration (6.41) with `X* = NumStochOpt.QuasiFejer.optimalSet f X` and
`V(x) = min_{x* ∈ X*} ‖x* - x‖²`: for every subsequence `x^{s_k} → x' ∉ X*` there is `ε₀ > 0`
such that for every `ε ∈ (0, ε₀)` and every `k` the sequence leaves the `ε`-ball around
`x^{s_k}`, and `limsup_k V(x^{τ_k}) < lim_k V(x^{s_k}) = V(x')`. -/
theorem lemma_p156_conditions_2b_3 {n : ℕ}
    (F : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (x g : ℕ → EuclideanSpace ℝ (Fin n)) (ρ : ℕ → ℝ) (C : ℝ)
    (hFconv : ∀ s, ConvexOn ℝ Set.univ (F s)) (hFcont : ∀ s, Continuous (F s))
    (hfconv : ConvexOn ℝ Set.univ f) (hfcont : Continuous f)
    (hXconv : Convex ℝ X) (hXcpt : IsCompact X) (hXne : X.Nonempty)
    (hunif : TendstoUniformlyOn F f atTop X)
    (hsub : ∀ s y, F s (x s) + ⟪g s, y - x s⟫ ≤ F s y)
    (hbound : ∀ s, ‖g s‖ ≤ C)
    (hrec : ∀ s, x (s + 1) = NumStochOpt.QuasiFejer.projX X (x s - ρ s • g s))
    (hρnn : ∀ s, 0 ≤ ρ s) (hρ0 : Tendsto ρ atTop (𝓝 0))
    (hρsum : Tendsto (fun N => ∑ s ∈ Finset.range N, ρ s) atTop atTop)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (x' : EuclideanSpace ℝ (Fin n))
    (hlim : Tendsto (x ∘ φ) atTop (𝓝 x')) (hx' : x' ∉ NumStochOpt.QuasiFejer.optimalSet f X) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      (∀ k, ∃ s, φ k ≤ s ∧ ε < ‖x s - x (φ k)‖) ∧
      limsup (fun k => Metric.infDist (x (exitTime x (φ k) ε)) (NumStochOpt.QuasiFejer.optimalSet f X) ^ 2) atTop
        < Metric.infDist x' (NumStochOpt.QuasiFejer.optimalSet f X) ^ 2 := by sorry

end NumStochOpt.Nonstationary
