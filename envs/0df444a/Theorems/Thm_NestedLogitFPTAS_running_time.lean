-- Prove2me | Theorems.Thm_NestedLogitFPTAS_running_time
-- name    : NestedLogitFPTAS.running_time
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:28:54.301036+00:00
-- url     : https://prove2.me/theorems/812a4475-c116-4ea4-9e42-3fb11f2ef02e
-- title:
--   §3.4 "Running time", p.14 (corrected: logarithms $L_w$, $L_r$ and the grids) — the operation count
-- statement:
--   There is a universal constant $K$ such that for every instance with $n$ products and every $\epsilon>0$ the program uses at most
--   $$
--   K\cdot n^3M^7\max(1,1/\epsilon)^8\cdot\frac{(\gamma^+)^{10}}{(\gamma^-)^3}\cdot L_w^6\cdot L_r^4
--   $$
--   operations, where $L_w=1+\log M+\log(W^\uparrow/W^\downarrow)$ and $L_r=1+\log M+\log(r_{\max}/(\pi_{\min}r_{\min}))$.
--
--   The state space has $O(M|\mathcal D_\omega||\mathcal D_\rho|)$ states, each state makes $O(|\mathcal D_\omega|^2|\mathcal D_\rho|^2)$ calls to the single-nest algorithm, and each call costs $O(n^3\gamma^+/\epsilon^2)$.
--
--   Differences from the source:
--   - encoding: products in pairwise-disjoint nests N₁, …, N_M; assortments S = (S₁, …, S_M); non-negative γₘ → Fin n with nest : Fin n → Fin M; S : Finset (Fin n) with Sₘ = part S m; 0 < M, nonempty nests, 0 < γₘ; reason: same instances wherever the paper is defined: at γₘ = 0 the ratio γ⁺/γ⁻ and the power ωₖ^{1/γₖ} are undefined, and W↓, r_min, π_min minimize over Nₘ
--   - generalization: signs of c, C, w₀ are not stated; w₀ read as a positive weight → c and C real of any sign, w₀ ≥ 0, w₀ₘ ≥ 0; R(∅) = 0 at w₀ = 0; reason: the proofs use no sign of c or C, and every instance with nonnegative costs and positive w₀ is covered
--   - encoding: any ϵ > 0 in the parameters ξω, ξρ, δω, δρ → the program uses ϵ̂ = min(ϵ, 1) in all its parameters; reason: no change for ϵ ≤ 1; the parameters need ϵ ≤ 80 and for ϵ ≥ 1 the guarantee is empty
--   - correction: Dω with p ≤ γ⁺·log_{1+ξω}(W↑/W↓); Dρ from π_min r_min W↓^{γ⁺} with q ≤ γ⁺·log_{1+ξρ}((r_max/(π_min r_min))(W↑/W↓)) → Pω = ⌈(γ⁺ log(W↑/W↓) + log M)/log(1+ξω)⌉ + M + 1; Lρ = (1−ξρ)^M π_min r_min W↓^{γ⁺}; Qρ = ⌈log(M r_max W↑^{γ⁺}/Lρ)/log(1+ξρ)⌉; reason: the printed tops cover one nest but the states hold sums: M = 2, one product per nest, r = w = c = 1, γ = 1, w₀ₘ = 0, w₀ = 2, C = 2 gives Dω = Dρ = {0, 1}, so R(S̃) ≤ 1/3 < (1−ϵ)/2 for ϵ < 1/3; and the printed bottom rounds (1−ξρ)·1 down to 0 there, so A(1, ω*₁, 0) = ∞ > c(S₁)
--   - correction: G over all subsets S ⊆ {1, …, t}; the search may return ∅ → the search reads G over nonempty subsets (an extra table); the recursion starts at t = 0; reason: one product with w = 0.05, r = 12, c = 1, w₀ₖ = 1, γₖ = 1, ωₖ = ρₖ = 1, δρ = 1/2, δω = 1/16: the neighbourhood is nonempty, but (η, ζ) = (0, 0) has G = 0, and ∅ is outside N_(2δω,20δρ)
--   - reading: running time of "our algorithm", no machine model; arithmetic operations and table accesses are counted in §3.4, §4.2 → operations charged in the instrumented program: unit-cost +, −, ×, /, ≤, ⌊·⌋, ⌈·⌉, Real.rpow, Real.log and array accesses; reason: exact w₊^γ is irrational for rational data, so this is the accounting the paper performs
--   - correction: log⁶(W↑/W↓)·log⁴(r_max/(π_min r_min)) → L_w⁶·L_r⁴ with L_w = 1 + log M + log(W↑/W↓), L_r = 1 + log M + log(r_max/(π_min r_min)); reason: the printed bound vanishes at W↑ = W↓ although the program does work there (the instance of the grid correction), and the corrected grids add log M; the exponents are the printed ones
-- source:
--   Segev, Approximation Schemes for Capacity-Constrained Assortment Optimization under the Nested Logit Model, SSRN #3553264 (Mar 2020), §3.4, "Running time", p.14

import Mathlib
import Definitions.Def_NestedLogitFPTAS_Model
import Definitions.Def_NestedLogitFPTAS_Grids
import Definitions.Def_NestedLogitFPTAS_Program

namespace NestedLogitFPTAS

/-- Segev, SSRN #3553264 (Mar 2020), §3.4, "Running time", p.14 (**corrected**): the program runs in
`O(n³M⁷/ϵ⁸ · (γ⁺)¹⁰/(γ⁻)³ · L_w⁶ · L_r⁴)` operations.

**Formalization Note.** `n` is the number of products. `K` is one constant before all the data. The
printed logarithms vanish at `W↑ = W↓`, so `L_w`, `L_r` add `1 + log M`, with the printed exponents.
`max 1 (1/ϵ)` is `1/ϵ̂`. -/
theorem running_time :
    ∃ K : ℝ, 0 < K ∧ ∀ {n M : ℕ} (I : Instance n M), I.Standing → ∀ ε : ℝ, 0 < ε →
      (I.ops ε : ℝ) ≤
        K * (n : ℝ) ^ 3 * (M : ℝ) ^ 7 * (max 1 (1 / ε)) ^ 8 *
          (I.gammaPlus ^ 10 / I.gammaMinus ^ 3) * I.Lw ^ 6 * I.Lr ^ 4 := by sorry

end NestedLogitFPTAS
