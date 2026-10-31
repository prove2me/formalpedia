-- Prove2me | Theorems.Thm_GuoZhaoADRC_theorem_3_1
-- name    : GuoZhaoADRC.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:41:52.669627+00:00
-- url     : https://prove2.me/theorems/9f770573-1bca-45c9-9134-6a5b06ec247f
-- title:
--   Theorem 3.1, p.1737 — global convergence of nonlinear ADRC: eventual observer and tracking errors $O(\varepsilon)$ (corrected: $a_{ik}$ constant, $|b^*|$, bounded reference)
-- statement:
--   Consider the MIMO system (1.1) under the extended state observer (1.5) with high gain $1/\varepsilon$ and the feedback ADRC(G) (3.2), that is, the closed loop (3.3). Assume (1.1), A1–A3 and GA1–GA3 (with the corrections listed below). Fix the system data ($f_i$, $F_0$, $a_{ik}$, $b_{ik}$, $\varphi_i$, $g^i_j$ and the Lyapunov data of A2–A3) and a bound $C$.
--
--   Then there are constants $\Gamma_1,\Gamma_2$ with the following property. For every disturbance $w$ and reference $z$ satisfying the hypotheses, with $\|w\|,\|\dot w\|,|z^i_j|,|\dot z^i_{n_i+1}|\le C$ on $[0,\infty)$, there is $\varepsilon_0>0$ such that for every $\varepsilon\in(0,\varepsilon_0)$ and every solution of (3.3) with parameter $\varepsilon$ there is a time $t_\varepsilon>0$, depending on $\varepsilon$ and the initial value, such that for all $t>t_\varepsilon$:
--
--   $$|x^i_j(t)-\hat x^i_j(t)|\le\Gamma_1\varepsilon^{n_i+2-j},\qquad 1\le j\le n_i+1,\ 1\le i\le m, \tag{3.4}$$
--
--   $$|x^i_j(t)-z^i_j(t)|\le\Gamma_2\varepsilon,\qquad 1\le j\le n_i,\ 1\le i\le m. \tag{3.5}$$
--
--   Here $x^i_{n_i+1}=f_i(x,\xi,w_i)+\sum_k(a_{ik}-b_{ik})u_k$ is the extended state (total disturbance). The constants $\Gamma_1,\Gamma_2$ do not depend on $\varepsilon$, on the initial value, or on the signals $w,z$ beyond the bound $C$.
--
--   So the observer recovers the state and the total disturbance, and the output tracks the reference, to accuracy $O(\varepsilon)$ from every initial value: a global separation principle for nonlinear ADRC.
--
--   **Formalization Note** Indices are 0-based, so $\varepsilon^{n_i+2-j}$ is `ε ^ (n i + 1 - j.val)`. The data's own signals are replaced by $w,\dot w,z,\dot z^i_{n_i+1}$ through a record update, and `ADRCHyp` is required of the updated data.
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
--   - reading: Γ₁, Γ₂ "independent of ε and the initial value. However, they are dependent on the bound of ‖z^i‖ and ‖(w, ẇ)‖" → Γ₁, Γ₂ chosen before ε, the solution and the signals w, z: uniform over all signals with a common bound C (which, by correction C3, also bounds ż^i_{n_i+1}); ε₀ chosen after the signals, t_ε after the solution; reason: the stronger of the two readings of the dependence sentence: Γ₁, Γ₂ depend on the signals only through their bounds
--   - encoding: "Let x(t, ε), x̂(t, ε) be the ε-dependent solutions of (3.3)" → every solution of (3.3) on [0, ∞) with parameter ε (existence is not asserted); reason: the theorem is a statement about every solution
--   - encoding: (3.5) ‖x^i_j − z^i_j‖ → |x^i_j − z^i_j|; reason: the quantities are scalars
--   - encoding: separate bounds on ‖z^i‖ and ‖(w, ẇ)‖ → one constant C bounding ‖w‖, ‖ẇ‖, every |z^i_j| and every |ż^i_{n_i+1}|; reason: given separate bounds take C as their maximum (the Euclidean ‖z^i‖ and the componentwise bound are equivalent)
-- source:
--   B.-Z. Guo, Z.-L. Zhao, On convergence of the nonlinear active disturbance rejection control for MIMO systems, SIAM J. Control Optim. 51(2) (2013) 1727–1757, doi:10.1137/110856824, Theorem 3.1, p.1737 (with GA1–GA3, (3.1), (3.2), (3.3), pp.1736–1737)

import Mathlib
import Definitions.Def_GuoZhaoADRC_ADRCData
import Definitions.Def_GuoZhaoADRC_ADRCHyp
import Definitions.Def_GuoZhaoADRC_IsClosedLoopSolution
import Definitions.Def_GuoZhaoADRC_fullState

namespace GuoZhaoADRC

/-- **Theorem 3.1 (global convergence of the nonlinear ADRC), corrected: `a_ik` constant,
`|b*_kl|` in (3.1), bounded reference.**
Guo–Zhao, SIAM J. Control Optim. 51 (2013), Theorem 3.1, p.1737.

Fix the system data (`f_i`, `F₀`, `a`, `b`, `φ_i`, `g^i_j` and the Lyapunov data of A2, A3) and
a bound `C`. There are constants `Γ₁, Γ₂` such that for every disturbance `w` and reference `z`
with `‖w‖, ‖ẇ‖, |z^i_j|, |ż^i_{n_i+1}| ≤ C` for which A1–A3 and GA1–GA3 hold (`ADRCHyp`, with the
corrections below), there is `ε₀ > 0` such that for every `ε ∈ (0, ε₀)` and every solution of
the closed loop (3.3) with parameter `ε` there is `t_ε > 0` with, for all `t > t_ε`,
(3.4) `|x^i_j(t) − x̂^i_j(t)| ≤ Γ₁ ε^{n_i+2−j}` for `1 ≤ j ≤ n_i + 1`, `1 ≤ i ≤ m`, and
(3.5) `|x^i_j(t) − z^i_j(t)| ≤ Γ₂ ε` for `1 ≤ j ≤ n_i`, `1 ≤ i ≤ m`,
where `x^i_{n_i+1} = f_i(x, ξ, w_i) + ∑_k (a_ik − b_ik)u_k` is the extended state.

**Formalization Note.** `Γ₁, Γ₂` are chosen before `ε`, the solution (so before its initial
value) and the signals `w`, `z`: they depend on `w`, `z` only through the bound `C` (the page:
"independent of ε and the initial value … dependent on the bound of ‖z^i‖ and ‖(w, ẇ)‖").
`ε₀` is chosen after the signals and `t_ε` after the solution. The data `D`'s own signals are
replaced by `w, w', z, zLast'`. Corrections (each with a counterexample to the printed
statement): GA2's `a_ik(w_i)` is a constant `a_ik`; (3.1) has `|b*_kl|`; A1 bounds all
components `z^i_1, …, z^i_{n_i+1}` and `ż^i_{n_i+1}`. Readings: `|g^i_j(r)| ≤ Λ^i_j|r|`;
`λ^i_11, λ^i_21, λ^i_23 > 0`; GA1 bounds the derivative of `f_i` in all its arguments.
0-based indices: the page's `j` is `j.val + 1`, so `ε^{n_i+2−j}` is `ε ^ (n i + 1 - j.val)`
and `z^i_j` is `z t i j.castSucc`. Solutions are required on `[0, ∞)` only. -/
theorem theorem_3_1 {m : ℕ} {n : Fin m → ℕ} {s : ℕ} (D : ADRCData m n s) (C : ℝ) :
    ∃ Γ₁ Γ₂ : ℝ,
      ∀ (w w' : ℝ → EuclideanSpace ℝ (Fin m)) (z : ℝ → (i : Fin m) → Fin (n i + 1) → ℝ)
        (zLast' : Fin m → ℝ → ℝ),
      let D' : ADRCData m n s := { D with w := w, w' := w', z := z, zLast' := zLast' }
      ADRCHyp D' →
      (∀ t, 0 ≤ t → ‖w t‖ ≤ C ∧ ‖w' t‖ ≤ C ∧ (∀ i j, |z t i j| ≤ C) ∧ ∀ i, |zLast' i t| ≤ C) →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ (x : ℝ → EuclideanSpace ℝ (Σ i : Fin m, Fin (n i))) (ξ : ℝ → EuclideanSpace ℝ (Fin s))
        (xhat : ℝ → (i : Fin m) → Fin (n i + 1) → ℝ), IsClosedLoopSolution D' ε x ξ xhat →
      ∃ tε : ℝ, 0 < tε ∧ ∀ t, tε < t →
        (∀ i (j : Fin (n i + 1)),
          |fullState D' x ξ xhat i t j - xhat t i j| ≤ Γ₁ * ε ^ (n i + 1 - j.val)) ∧
        (∀ i (j : Fin (n i)), |x t ⟨i, j⟩ - z t i j.castSucc| ≤ Γ₂ * ε) := by sorry

end GuoZhaoADRC
