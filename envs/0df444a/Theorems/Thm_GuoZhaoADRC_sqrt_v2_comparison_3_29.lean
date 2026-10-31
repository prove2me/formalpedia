-- Prove2me | Theorems.Thm_GuoZhaoADRC_sqrt_v2_comparison_3_29
-- name    : GuoZhaoADRC.sqrt_v2_comparison_3_29
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:43:01.675606+00:00
-- url     : https://prove2.me/theorems/61c6a5da-8050-4c3a-b5ad-3655739fae0e
-- title:
--   Eqs. (3.28)–(3.29), p.1741 — comparison bound for $\sqrt{V_2(\eta)}$ (corrected: $V\to V_2$)
-- statement:
--   Assume the hypotheses of Theorem 3.1. Let $\Gamma_1\ge0$, $\varepsilon\in(0,1]$ and $t_\varepsilon\ge0$, and take a solution of (3.3) with $\|e^i(t)\|\le\Gamma_1\varepsilon$ for all $t>t_\varepsilon$ and all $i$. Put
--
--   $$c_2=\frac12\min_i\frac{\lambda^i_{23}}{\lambda^i_{22}},\qquad K_2=\frac{\sum_{i=1}^m\beta^i_2(L_i+1)\Gamma_1\varepsilon}{2\sqrt{\min_i\lambda^i_{21}}}.$$
--
--   Then for every $t\ge t_\varepsilon$,
--
--   $$\sqrt{V_2(\eta(t))}\le e^{-c_2(t-t_\varepsilon)}\sqrt{V_2(\eta(t_\varepsilon))}+K_2\int_{t_\varepsilon}^te^{-c_2(t-s)}\,ds.$$
--
--   The tracking error therefore settles at a level of order $K_2/c_2\sim\varepsilon$, which with (1.6) gives (3.5) of Theorem 3.1.
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
--   - correction: (3.29): √V(η) and √V(η(t_ε)) → √V₂(η) and √V₂(η(t_ε)); reason: V is the composite function (3.10) of (η, e); the comparison is for V₂ of (1.7), as in (3.28)
--   - reading: ε ∈ (0, ε₀) with ε₀ = min{1, …} ≤ 1 → ε ≤ 1 assumed; reason: the estimates ‖x̃^i − x^i‖ ≤ ‖e^i‖ and |ε^{n_l−j} g^l_j(e^l_1)| ≤ Λ^l_j‖e‖ need ε ≤ 1, which the page has through ε₀ ≤ 1 (3.18)
--   - generalization: conclusion for t > t_ε → conclusion for t ≥ t_ε; reason: at t = t_ε the bound is trivial
-- source:
--   B.-Z. Guo, Z.-L. Zhao, On convergence of the nonlinear active disturbance rejection control for MIMO systems, SIAM J. Control Optim. 51(2) (2013) 1727–1757, doi:10.1137/110856824, eqs. (3.28)–(3.29), p.1741

import Mathlib
import Definitions.Def_GuoZhaoADRC_ADRCData
import Definitions.Def_GuoZhaoADRC_ADRCHyp
import Definitions.Def_GuoZhaoADRC_IsClosedLoopSolution
import Definitions.Def_GuoZhaoADRC_scaledErr
import Definitions.Def_GuoZhaoADRC_trackErr
import Definitions.Def_GuoZhaoADRC_lyapV2
import Definitions.Def_GuoZhaoADRC_minOver

namespace GuoZhaoADRC

/-- **The comparison bound (3.29) for `√V_2(η)` (V → V₂ corrected).**
Guo–Zhao, SIAM J. Control Optim. 51 (2013), eqs. (3.28)–(3.29), p.1741.

Let `Γ₁ ≥ 0`, `ε ∈ (0, 1]`, `t_ε ≥ 0`, and take a solution of (3.3) with `‖e^i(t)‖ ≤ Γ₁ε`
for all `t > t_ε` and all `i`. Then, with `c₂ = min_i(λ^i_23/λ^i_22)/2` and
`K₂ = ∑_i β^i_2(L_i + 1)Γ₁ε/(2√(min_i λ^i_21))`, for every `t ≥ t_ε`:
`√V_2(η(t)) ≤ e^{−c₂(t−t_ε)} √V_2(η(t_ε)) + K₂ ∫_{t_ε}^t e^{−c₂(t−s)} ds`.

**Formalization Note.** The page writes `√V(η)`; `V` there is `V_2` of (1.7), not the
composite `V` of (3.10). -/
theorem sqrt_v2_comparison_3_29 {m : ℕ} {n : Fin m → ℕ} {s : ℕ} (D : ADRCData m n s)
    (hD : ADRCHyp D) (Γ₁ : ℝ) (hΓ₁ : 0 ≤ Γ₁) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (tε : ℝ) (htε : 0 ≤ tε)
    (x : ℝ → EuclideanSpace ℝ (Σ i : Fin m, Fin (n i))) (ξ : ℝ → EuclideanSpace ℝ (Fin s))
    (xhat : ℝ → (i : Fin m) → Fin (n i + 1) → ℝ) (hsol : IsClosedLoopSolution D ε x ξ xhat)
    (he : ∀ t, tε < t → ∀ i, ‖scaledErr D ε x ξ xhat t i‖ ≤ Γ₁ * ε) :
    ∀ t, tε ≤ t →
      Real.sqrt (lyapV2 D (trackErr D x t)) ≤
        Real.exp (-(minOver D.hm (fun i => D.lam23 i / D.lam22 i) / 2) * (t - tε)) *
            Real.sqrt (lyapV2 D (trackErr D x tε)) +
          (∑ i, D.beta2 i * ((D.L i : ℝ) + 1) * Γ₁ * ε) / (2 * Real.sqrt (minOver D.hm D.lam21)) *
            ∫ σ in tε..t, Real.exp (-(minOver D.hm (fun i => D.lam23 i / D.lam22 i) / 2) * (t - σ)) := by sorry

end GuoZhaoADRC
