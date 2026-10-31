-- Prove2me | Theorems.Thm_GuoZhaoADRC_delta_bar_bound_3_9
-- name    : GuoZhaoADRC.delta_bar_bound_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:43:00.765625+00:00
-- url     : https://prove2.me/theorems/8a7a7025-99cb-4bd7-b835-a30a680be026
-- title:
--   Eqs. (3.7)–(3.9), p.1738 — the bound $|\bar\Delta_i|\le\Xi^i_0+\Xi^i_1\|e\|+\Xi^i_2\|\eta\|+(\Xi^i/\varepsilon)\|e\|$ (corrected: $\Xi^i_2$, $|b^*|$, $a_{ik}$ constant)
-- statement:
--   Assume the hypotheses of Theorem 3.1. There are positive constants $\Xi^i_0,\Xi^i_1,\Xi^i_2$ ($1\le i\le m$), independent of $\varepsilon$ and of the solution, such that for every $\varepsilon\in(0,1]$, every solution of the closed loop (3.3) with parameter $\varepsilon$, every $t\ge0$ and every derivative $\bar\Delta_i$ at $t$ of the extended state $x^i_{n_i+1}=f_i(x,\xi,w_i)+\sum_k(a_{ik}-b_{ik})u_k$,
--
--   $$|\bar\Delta_i|\le\Xi^i_0+\Xi^i_1\|e\|+\Xi^i_2\|\eta\|+\frac{\Xi^i}{\varepsilon}\|e\|,\qquad \Xi^i=\sqrt m\sum_{k,l=1}^m|a_{ik}-b_{ik}|\,|b^*_{kl}|\,\Lambda^l_{n_l+1}.$$
--
--   Here $e$ and $\eta$ are the stacked scaled observer and tracking errors with their Euclidean norms. The bound says that the total disturbance changes at a rate controlled by the errors, with a single term of order $1/\varepsilon$ coming from the gain mismatch; condition (3.1) makes that term small enough for the observer to absorb it.
--
--   **Formalization Note** $\bar\Delta_i$ is any derivative of the extended state within $[0,\infty)$; since $\varphi_i$ is only Lipschitz, the derivative need not exist at every time, and the bound is claimed wherever it does.
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
--   - correction: (3.9): Ξ^j_2‖η‖ → Ξ^i_2‖η‖; reason: typo: the constant belongs to subsystem i (no index j is in scope)
--   - correction: (3.9): Ξ^i = √m Σ_{k,l} sup_t |a_ik(w_i(t)) − b_ik| b*_kl Λ^l_{n_l+1} → Ξ^i = √m Σ_{k,l} |a_ik − b_ik| |b*_kl| Λ^l_{n_l+1}; reason: consequence of the corrections of GA2 (a_ik constant) and of (3.1) (|b*_kl|); with time-varying a_ik(w_i) and unbounded ξ the printed bound is false (the term ȧ_ik ẇ_i b*_kl u*_l of (3.8) is not bounded by the right side)
--   - reading: ε ∈ (0, ε₀) with ε₀ = min{1, …} ≤ 1 → ε ≤ 1 assumed; reason: the estimates ‖x̃^i − x^i‖ ≤ ‖e^i‖ and |ε^{n_l−j} g^l_j(e^l_1)| ≤ Λ^l_j‖e‖ need ε ≤ 1, which the page has through ε₀ ≤ 1 (3.18)
--   - generalization: Δ̄_i = d/dt x^i_{n_i+1} along (3.3), tacitly differentiable (the page differentiates φ_i in (3.8)) → the claim is made at every t and for every derivative Δ of the extended state within [0, ∞) at t, wherever one exists; reason: φ_i is only Lipschitz (A3), so the extended state is only locally Lipschitz in t; where the page's derivative exists the two statements agree
-- source:
--   B.-Z. Guo, Z.-L. Zhao, On convergence of the nonlinear active disturbance rejection control for MIMO systems, SIAM J. Control Optim. 51(2) (2013) 1727–1757, doi:10.1137/110856824, eqs. (3.7)–(3.9), p.1738

import Mathlib
import Definitions.Def_GuoZhaoADRC_ADRCData
import Definitions.Def_GuoZhaoADRC_ADRCHyp
import Definitions.Def_GuoZhaoADRC_IsClosedLoopSolution
import Definitions.Def_GuoZhaoADRC_extState
import Definitions.Def_GuoZhaoADRC_scaledErr
import Definitions.Def_GuoZhaoADRC_trackErr
import Definitions.Def_GuoZhaoADRC_stackNorm
import Definitions.Def_GuoZhaoADRC_Xi

namespace GuoZhaoADRC

/-- **The bound (3.9) on the derivative `Δ̄_i` of the extended state.**
Guo–Zhao, SIAM J. Control Optim. 51 (2013), eqs. (3.7)–(3.9), p.1738.

There are positive constants `Ξ^i_0, Ξ^i_1, Ξ^i_2`, independent of `ε` and of the solution, such
that for every `ε ∈ (0, 1]`, every solution of (3.3) with parameter `ε`, every `t ≥ 0` and every
derivative `Δ̄_i` of `t ↦ x^i_{n_i+1}(t)` at `t`:
`|Δ̄_i| ≤ Ξ^i_0 + Ξ^i_1‖e‖ + Ξ^i_2‖η‖ + (Ξ^i/ε)‖e‖`, with `Ξ^i` of (3.9) (`Xi`).

**Formalization Note.** `Δ̄_i` is any derivative within `[0, ∞)` of the extended state; since
`φ_i` is only Lipschitz the derivative need not exist at every `t`, and the bound is claimed
wherever it does. `‖e‖`, `‖η‖` are the Euclidean norms of the stacked vectors. -/
theorem delta_bar_bound_3_9 {m : ℕ} {n : Fin m → ℕ} {s : ℕ} (D : ADRCData m n s)
    (hD : ADRCHyp D) :
    ∃ Ξ₀ Ξ₁ Ξ₂ : Fin m → ℝ, (∀ i, 0 < Ξ₀ i ∧ 0 < Ξ₁ i ∧ 0 < Ξ₂ i) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ (x : ℝ → EuclideanSpace ℝ (Σ i : Fin m, Fin (n i))) (ξ : ℝ → EuclideanSpace ℝ (Fin s))
        (xhat : ℝ → (i : Fin m) → Fin (n i + 1) → ℝ), IsClosedLoopSolution D ε x ξ xhat →
      ∀ t, 0 ≤ t → ∀ i (Δ : ℝ),
        HasDerivWithinAt (fun τ => extState D x ξ xhat i τ) Δ (Set.Ici 0) t →
        |Δ| ≤ Ξ₀ i + Ξ₁ i * stackNorm (scaledErr D ε x ξ xhat t) +
          Ξ₂ i * stackNorm (trackErr D x t) + Xi D i / ε * stackNorm (scaledErr D ε x ξ xhat t) := by sorry

end GuoZhaoADRC
