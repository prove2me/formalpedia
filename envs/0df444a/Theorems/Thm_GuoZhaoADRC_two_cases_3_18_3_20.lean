-- Prove2me | Theorems.Thm_GuoZhaoADRC_two_cases_3_18_3_20
-- name    : GuoZhaoADRC.two_cases_3_18_3_20
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:43:22.908246+00:00
-- url     : https://prove2.me/theorems/73a4f23e-3f57-4002-b865-8dd7493b2e91
-- title:
--   Eqs. (3.18)–(3.20), pp.1739–1740 — outside the ball of radius $R$: $\dot V<0$ if $\|e\|\ge R/2$, $\dot V\le0$ otherwise (corrected: $\Pi_2\to\Pi_4$ in $\varepsilon_0$)
-- statement:
--   Assume the hypotheses of Theorem 3.1. Let $\Xi^i_0,\Xi^i_1,\Xi^i_2\ge0$, and let
--
--   $$R=\max\Bigl\{2,\frac{2\Pi_3}{\lambda}\Bigr\},\qquad 0<\varepsilon<\varepsilon_0=\min\Bigl\{1,\varepsilon_1,\frac{\Pi_1}{4\Pi_3},\frac{\lambda\Pi_1}{8\Pi_4^2}\Bigr\}.$$
--
--   Take a solution of (3.3) and $t\ge0$ at which every extended state has a derivative satisfying the bound (3.9), and assume $\|(e,\eta)\|=(\|e\|^2+\|\eta\|^2)^{1/2}\ge R$. Then every derivative of $V$ (3.10) at $t$ satisfies:
--
--   1. (Case 1, (3.19)) if $\|e\|\ge R/2$, then $\dfrac{dV}{dt}\le-\Bigl(\dfrac{\Pi_1}{4\varepsilon}-\Pi_3\Bigr)<0$;
--   2. (Case 2, (3.20)) if $\|e\|<R/2$, then $\dfrac{dV}{dt}\le0$.
--
--   So $V$ does not increase outside the ball of radius $R$, a radius independent of $\varepsilon$.
--
--   **Formalization Note** $\varepsilon<\varepsilon_0$ is written without division: $\varepsilon<1$, $2\varepsilon\Pi_2<\Pi_1$, $4\varepsilon\Pi_3<\Pi_1$, $8\varepsilon\Pi_4^2<\lambda\Pi_1$. $\lambda>0$ and $\Pi_1>0$ follow from A3 and (3.1).
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
--   - correction: (3.18): ε₀ = min{1, ε₁, Π₁/(4Π₃), λΠ₁/(8Π₂²)} → 8εΠ₄² < λΠ₁ (corrected Π₄); reason: the term 4εΠ²/Π₁ of (3.17) has Π₄, not Π₂ (see (3.16)); ε₀ must make it ≤ λ/2
--   - correction: (3.20): −(λ − 4εΠ₂²/Π₁)‖η‖² ≤ −(λ − 4εΠ₂²/Π₁)R², using ‖η‖ ≥ R → conclusion dV/dt ≤ 0 stated, without the intermediate chain; reason: Case 2 only shows ‖η‖ ≥ R/2, so the printed middle step does not follow; the conclusion survives because ‖e‖ < R/2 and ‖(e, η)‖ ≥ R give ‖η‖² ≥ 3R²/4, and then Π₃‖e‖ − (λ/2)‖η‖² ≤ R(Π₃/2 − 3λR/8) ≤ 0
--   - encoding: ε ∈ (0, ε₀) with ε₀ given by divisions → ε < 1, 2εΠ₂ < Π₁, 4εΠ₃ < Π₁, 8εΠ₄² < λΠ₁; reason: equivalent for Π₂, Π₃, Π₄ > 0 and meaningful when one of them vanishes
--   - encoding: ‖e, η‖ ≥ R → √(‖e‖² + ‖η‖²) ≥ R; reason: the Euclidean norm of the pair (e, η)
--   - generalization: Ξ^i_0, Ξ^i_1, Ξ^i_2 are the ε-independent positive constants of (3.9), with (3.9) holding along the solution → Ξ^i_0, Ξ^i_1, Ξ^i_2 are any nonnegative constants, and the bound (3.9) is assumed only at the time t, for the derivatives Δ_i of the extended states; reason: the constants of (3.9) are positive and satisfy (3.9) at every time, so they are an instance
--   - generalization: Δ̄_i = d/dt x^i_{n_i+1} along (3.3), tacitly differentiable (the page differentiates φ_i in (3.8)) → the claim is made at every t and for every derivative Δ of the extended state within [0, ∞) at t, wherever one exists; reason: φ_i is only Lipschitz (A3), so the extended state is only locally Lipschitz in t; where the page's derivative exists the two statements agree
-- source:
--   B.-Z. Guo, Z.-L. Zhao, On convergence of the nonlinear active disturbance rejection control for MIMO systems, SIAM J. Control Optim. 51(2) (2013) 1727–1757, doi:10.1137/110856824, eqs. (3.18)–(3.20), pp.1739–1740

import Mathlib
import Definitions.Def_GuoZhaoADRC_ADRCData
import Definitions.Def_GuoZhaoADRC_ADRCHyp
import Definitions.Def_GuoZhaoADRC_IsClosedLoopSolution
import Definitions.Def_GuoZhaoADRC_extState
import Definitions.Def_GuoZhaoADRC_scaledErr
import Definitions.Def_GuoZhaoADRC_trackErr
import Definitions.Def_GuoZhaoADRC_stackNorm
import Definitions.Def_GuoZhaoADRC_lyapV1
import Definitions.Def_GuoZhaoADRC_lyapV2
import Definitions.Def_GuoZhaoADRC_Xi
import Definitions.Def_GuoZhaoADRC_Pi1
import Definitions.Def_GuoZhaoADRC_Pi2
import Definitions.Def_GuoZhaoADRC_Pi3
import Definitions.Def_GuoZhaoADRC_Pi4
import Definitions.Def_GuoZhaoADRC_lamMin

namespace GuoZhaoADRC

/-- **The two cases (3.19)–(3.20) outside the ball of radius `R` (3.18).**
Guo–Zhao, SIAM J. Control Optim. 51 (2013), eqs. (3.18)–(3.20), pp.1739–1740.

Let `R = max{2, 2Π₃/λ}` and `ε ∈ (0, ε₀)`, `ε₀ = min{1, ε₁, Π₁/(4Π₃), λΠ₁/(8Π₄²)}`. Under the
hypotheses of (3.15) at `t`, if `‖(e, η)‖ ≥ R` then
(Case 1) `‖e‖ ≥ R/2` implies `dV/dt ≤ −(Π₁/(4ε) − Π₃) < 0`, and
(Case 2) `‖e‖ < R/2` implies `dV/dt ≤ 0`.

**Formalization Note.** `ε < ε₀` is written without division: `ε < 1`, `2εΠ₂ < Π₁`,
`4εΠ₃ < Π₁`, `8εΠ₄² < λΠ₁` (with the corrected `Π₄`). `‖(e, η)‖ = (‖e‖² + ‖η‖²)^{1/2}`.
`λ > 0` and `Π₁ > 0` follow from A3 and (3.1). -/
theorem two_cases_3_18_3_20 {m : ℕ} {n : Fin m → ℕ} {s : ℕ} (D : ADRCData m n s)
    (hD : ADRCHyp D) (Ξ₀ Ξ₁ Ξ₂ : Fin m → ℝ) (hΞ₀ : ∀ i, 0 ≤ Ξ₀ i) (hΞ₁ : ∀ i, 0 ≤ Ξ₁ i)
    (hΞ₂ : ∀ i, 0 ≤ Ξ₂ i) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hε₁ : 2 * ε * Pi2 D Ξ₁ < Pi1 D) (hε₂ : 4 * ε * Pi3 D Ξ₀ < Pi1 D)
    (hε₃ : 8 * ε * Pi4 D Ξ₂ ^ 2 < lamMin D * Pi1 D)
    (x : ℝ → EuclideanSpace ℝ (Σ i : Fin m, Fin (n i))) (ξ : ℝ → EuclideanSpace ℝ (Fin s))
    (xhat : ℝ → (i : Fin m) → Fin (n i + 1) → ℝ) (hsol : IsClosedLoopSolution D ε x ξ xhat)
    (t : ℝ) (ht : 0 ≤ t) (Δ : Fin m → ℝ)
    (hΔ : ∀ i, HasDerivWithinAt (fun τ => extState D x ξ xhat i τ) (Δ i) (Set.Ici 0) t)
    (hΔbound : ∀ i, |Δ i| ≤ Ξ₀ i + Ξ₁ i * stackNorm (scaledErr D ε x ξ xhat t) +
      Ξ₂ i * stackNorm (trackErr D x t) + Xi D i / ε * stackNorm (scaledErr D ε x ξ xhat t))
    (DV : ℝ) (hDV : HasDerivWithinAt
      (fun τ => lyapV1 D (scaledErr D ε x ξ xhat τ) + lyapV2 D (trackErr D x τ)) DV (Set.Ici 0) t)
    (hR : max 2 (2 * Pi3 D Ξ₀ / lamMin D) ≤
      Real.sqrt (stackNorm (scaledErr D ε x ξ xhat t) ^ 2 + stackNorm (trackErr D x t) ^ 2)) :
    (max 2 (2 * Pi3 D Ξ₀ / lamMin D) / 2 ≤ stackNorm (scaledErr D ε x ξ xhat t) →
      DV ≤ -(Pi1 D / (4 * ε) - Pi3 D Ξ₀) ∧ -(Pi1 D / (4 * ε) - Pi3 D Ξ₀) < 0) ∧
    (stackNorm (scaledErr D ε x ξ xhat t) < max 2 (2 * Pi3 D Ξ₀ / lamMin D) / 2 → DV ≤ 0) := by sorry

end GuoZhaoADRC
