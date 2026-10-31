-- Prove2me | Theorems.Thm_GuoZhaoADRC_sqrt_v1_comparison_3_23
-- name    : GuoZhaoADRC.sqrt_v1_comparison_3_23
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:43:59.027321+00:00
-- url     : https://prove2.me/theorems/3c92c645-1a47-419b-be99-2101fef19938
-- title:
--   Eqs. (3.22)–(3.23), p.1740 — comparison bound for $\sqrt{V_1(e)}$ (corrected: factor $\sqrt{V_1(e(\tau_\varepsilon))}$)
-- statement:
--   Assume the hypotheses of Theorem 3.1. Let $M_1,\dots,M_m\ge0$, $\varepsilon>0$ and $\tau\ge0$, and take a solution of (3.3) such that for every $t>\tau$ and every derivative $\bar\Delta_i$ of the extended state at $t$, $|\bar\Delta_i|\le M_i+(\Xi^i/\varepsilon)\|e(t)\|$. Put
--
--   $$c=\frac{\Pi_1}{2\varepsilon\max_i\lambda^i_{12}},\qquad K=\frac{\sum_{i=1}^mM_i\beta^i_1}{2\sqrt{\min_i\lambda^i_{11}}}.$$
--
--   Then for every $t\ge\tau$,
--
--   $$\sqrt{V_1(e(t))}\le e^{-c(t-\tau)}\sqrt{V_1(e(\tau))}+K\int_\tau^te^{-c(t-s)}\,ds.$$
--
--   The observer error forgets its initial value at rate $c\sim1/\varepsilon$ and settles at a level of order $K/c\sim\varepsilon$.
--
--   **Formalization Note** The bound on $\bar\Delta_i$ is required only at the times where the derivative exists.
--
--   Differences from the source:
--   - correction: GA2: a_ik(x, ξ, w_i) = a_ik(w_i), varying in time through w_i(t), with sup_t in (3.1) → a_ik are constants; reason: as printed, Theorem 3.1 is false: m = n₁ = s = 1, ξ̇ = 1, f₁ = ξ, w = sin t, a₁₁ = 1 + w/10, b₁₁ = 1, φ(y) = −y, z ≡ 0, g₁(r) = 2r, g₂(r) = r satisfy every printed assumption (A2 with V₁ = yᵀPy, P = [[1/2, −1/2], [−1/2, 3/2]]; (3.1) reads 0.68 > 0), but (3.8) contains ȧ_ik ẇ_i b*_kl u*_l and u*_l must cancel f_l = ξ, which grows; simulating (3.3) with ε = 0.02 gives max |x₁ − z₁| over successive windows of length 100 equal to 0.33, 0.63, …, 3.00 by t = 1000, growing linearly in t, so no bound Γ₂ε holds
--   - correction: (3.1) and Ξ^i of (3.9) with b*_kl (signed) → |b*_kl|; reason: replacing (a, b) by (−a, −b) leaves the closed loop unchanged but flips the sign of the printed sum, so the signed condition holds for one sign choice of any system: m = n₁ = 1, f ≡ 0, w ≡ 0, z ≡ 0, φ(y) = −y, g₁(r) = 2r, g₂(r) = r, a = 1, b = −1 satisfies the signed (3.1) (1 + 2·3.162 > 0), yet the closed-loop matrix in (x₁, x̂₁, x̂₂) has the eigenvalue 42.8 at ε = 0.01 (415.6 at ε = 0.001) with an eigenvector whose x₁-component is nonzero, so |x₁ − z₁| → ∞; the proof bounds |(a − b)b*| by |a − b||b*|
--   - correction: A1: ‖(z^i_1, …, z^i_{n_i})‖ < C₁ (the TD state without its last component) → every component z^i_j, 1 ≤ j ≤ n_i + 1, and the derivative ż^i_{n_i+1} are bounded on [0, ∞); reason: the feedback uses z^i_{n_i+1} and (3.8) contains ż^l_{n_l+1}; for m = n₁ = 1, f(x) = x₁, a = b = 1, φ(y) = −y, g as above, a TD solution (ψ(r₁, r₂) = −r₁ − r₂, ρ = 1, v = z₁ + ż₁ + z̈₁) whose z₁ is a train of unit bumps at t = k of width 1/k² satisfies A1 with C₁ = 2 while z₂ = ż₁ is unbounded; each rising flank moves x₂ − x̂₂ by about 1 at arbitrarily late times, so |x₂ − x̂₂| ≤ Γ₁ε fails
--   - generalization: z^i is the solution of the tracking differentiator (1.3) → z^i is any signal on [0, ∞) with ż^i_j = z^i_{j+1} (1 ≤ j ≤ n_i) and z^i_{n_i+1} differentiable; reason: every TD solution has this integrator chain, and so does Remark 1.1's choice z^i_j = v_i^{(j−1)}; the statement for all such signals specializes to the TD
--   - reading: A2: |g^i_j(r)| ≤ Λ^i_j r for all r ∈ ℝ → |g^i_j(r)| ≤ Λ^i_j |r|; reason: as printed the condition forces every g^i_j to vanish on a half-line (|g| ≤ Λr ≤ 0 there), so it excludes every linear gain g^i_j(r) = kr with k ≠ 0, the linear ESO the page itself calls a special case (p.1729); when all Λ^i_j have one sign, A2 (2) moreover fails at y = (y₁, 0, …, 0) with y₁ in that half-line, so A2 would be unsatisfiable; |r| is the only meaningful reading
--   - reading: A2, A3: λ^i_11, λ^i_21, λ^i_23 are "constants" → λ^i_11 > 0, λ^i_21 > 0, λ^i_23 > 0; reason: the proof divides by min λ^i_11, min λ^i_21 and λ = min λ^i_23 ((3.18), (3.21)–(3.29)); positivity is the standard meaning of these quadratic Lyapunov bounds
--   - reading: GA1: all partial derivatives of f_i are bounded "over ℝ^{n+m}" → the Fréchet derivative of (x, ξ, w_i) ↦ f_i(x, ξ, w_i) is bounded in operator norm; reason: the printed domain fits none of f_i's argument lists; the proof uses ∂f_i/∂x, ∂f_i/∂ξ (in L_{F₀}f_i) and ∂f_i/∂w_i with ξ unbounded; in finite dimension bounded partial derivatives and a bounded Fréchet derivative are equivalent
--   - generalization: w is C¹ with sup_{t≥0} ‖(w, ẇ)‖ < ∞ → w is differentiable on [0, ∞) with ‖w‖ and ‖ẇ‖ bounded (continuity of ẇ not required); reason: continuity of ẇ is never used; C¹ disturbances satisfy the Lean hypothesis
--   - generalization: zero dynamics ξ ∈ ℝ^s (tacitly s ≥ 1); g^i_j "possibly some nonlinear functions" → s = 0 allowed; g^i_j arbitrary functions with only the A2 bound; reason: s = 0 is the system without zero dynamics and the statement for s ≥ 1 is a special case; the page states no regularity for g^i_j and Lean adds none
--   - encoding: 1-based indices i, j; ℝ^{n_i}, ℝ^{n_i+1}, ℝ^n, ℝ^s, ℝ^m with ‖·‖ → 0-based Fin indices (page j ↔ Lean j − 1, page n_i + 1 ↔ Fin.last (n i)); EuclideanSpace, so every norm is Euclidean; ‖e‖, ‖η‖ are Euclidean norms of the stacked vectors; reason: Lean convention; same instances
--   - encoding: solutions of (3.3) and time derivatives along them → HasDerivWithinAt … (Set.Ici 0) t at every t ≥ 0 (one-sided at t = 0, nothing required for t < 0); reason: the closed loop starts at t = 0; same solutions on [0, ∞)
--   - encoding: A2, A3: positive definite; A2 (1) "∀ y ∈ ℝ^{n+1}"; A2 (3) max{|∂_{n_i}V₁^i|, |∂_{n_i+1}V₁^i|} ≤ β^i_1‖y‖; (b*_kl) = (b_ij)⁻¹; sup ‖(w, ẇ)‖ < ∞ → V(0) = 0 ∧ V(y) > 0 for y ≠ 0; ∀ y ∈ ℝ^{n_i+1} (the domain of V₁^i); the two bounds separately; b⁻¹ with det b a unit; separate bounds on ‖w‖ and ‖ẇ‖; reason: equivalent formulations; same instances
--   - correction: (3.23): first term e^{−c(t−τ_ε)} → e^{−c(t−τ)}√V₁(e(τ)); reason: the comparison principle gives the initial value √V₁(e(τ_ε)) as a factor; without it the bound fails for large initial errors (take M = 0 and V₁(e(τ)) > 1)
--   - generalization: τ_ε of the ultimate bound, ε ∈ (0, ε₀), conclusion for t > τ_ε → any τ ≥ 0 and ε > 0 with the derivative bound on (τ, ∞); conclusion for t ≥ τ; reason: the page's situation is an instance; at t = τ the bound is trivial
--   - generalization: Δ̄_i = d/dt x^i_{n_i+1} along (3.3), tacitly differentiable (the page differentiates φ_i in (3.8)) → the claim is made at every t and for every derivative Δ of the extended state within [0, ∞) at t, wherever one exists; reason: φ_i is only Lipschitz (A3), so the extended state is only locally Lipschitz in t; where the page's derivative exists the two statements agree
-- source:
--   B.-Z. Guo, Z.-L. Zhao, On convergence of the nonlinear active disturbance rejection control for MIMO systems, SIAM J. Control Optim. 51(2) (2013) 1727–1757, doi:10.1137/110856824, eqs. (3.22)–(3.23), p.1740

import Mathlib
import Definitions.Def_GuoZhaoADRC_ADRCData
import Definitions.Def_GuoZhaoADRC_ADRCHyp
import Definitions.Def_GuoZhaoADRC_IsClosedLoopSolution
import Definitions.Def_GuoZhaoADRC_extState
import Definitions.Def_GuoZhaoADRC_scaledErr
import Definitions.Def_GuoZhaoADRC_stackNorm
import Definitions.Def_GuoZhaoADRC_lyapV1
import Definitions.Def_GuoZhaoADRC_Xi
import Definitions.Def_GuoZhaoADRC_Pi1
import Definitions.Def_GuoZhaoADRC_minOver
import Definitions.Def_GuoZhaoADRC_maxOver

namespace GuoZhaoADRC

/-- **The comparison bound (3.23) for `√V_1(e)` (missing factor corrected).**
Guo–Zhao, SIAM J. Control Optim. 51 (2013), eqs. (3.22)–(3.23), p.1740.

Let `M_i ≥ 0`, `ε > 0`, `τ ≥ 0`, and take a solution of (3.3) such that for every `t > τ`
and every derivative `Δ̄_i` of the extended state at `t`, `|Δ̄_i| ≤ M_i + (Ξ^i/ε)‖e(t)‖`.
Then, with `c = Π₁/(2ε max_i λ^i_12)` and `K = ∑_i M_iβ^i_1/(2√(min_i λ^i_11))`, for every
`t ≥ τ`:
`√V_1(e(t)) ≤ e^{−c(t−τ)} √V_1(e(τ)) + K ∫_τ^t e^{−c(t−s)} ds`.

**Formalization Note.** The page's first term lacks the factor `√V_1(e(τ_ε))`. The bound on
`Δ̄_i` is required only where the derivative exists. -/
theorem sqrt_v1_comparison_3_23 {m : ℕ} {n : Fin m → ℕ} {s : ℕ} (D : ADRCData m n s)
    (hD : ADRCHyp D) (M : Fin m → ℝ) (hM : ∀ i, 0 ≤ M i) (ε : ℝ) (hε : 0 < ε)
    (τ : ℝ) (hτ : 0 ≤ τ)
    (x : ℝ → EuclideanSpace ℝ (Σ i : Fin m, Fin (n i))) (ξ : ℝ → EuclideanSpace ℝ (Fin s))
    (xhat : ℝ → (i : Fin m) → Fin (n i + 1) → ℝ) (hsol : IsClosedLoopSolution D ε x ξ xhat)
    (hΔ : ∀ t, τ < t → ∀ i (Δ : ℝ),
      HasDerivWithinAt (fun σ => extState D x ξ xhat i σ) Δ (Set.Ici 0) t →
      |Δ| ≤ M i + Xi D i / ε * stackNorm (scaledErr D ε x ξ xhat t)) :
    ∀ t, τ ≤ t →
      Real.sqrt (lyapV1 D (scaledErr D ε x ξ xhat t)) ≤
        Real.exp (-(Pi1 D / (2 * ε * maxOver D.hm D.lam12)) * (t - τ)) *
            Real.sqrt (lyapV1 D (scaledErr D ε x ξ xhat τ)) +
          (∑ i, M i * D.beta1 i) / (2 * Real.sqrt (minOver D.hm D.lam11)) *
            ∫ σ in τ..t, Real.exp (-(Pi1 D / (2 * ε * maxOver D.hm D.lam12)) * (t - σ)) := by sorry

end GuoZhaoADRC
