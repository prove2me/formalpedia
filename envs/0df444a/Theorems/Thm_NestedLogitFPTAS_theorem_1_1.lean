-- Prove2me | Theorems.Thm_NestedLogitFPTAS_theorem_1_1
-- name    : NestedLogitFPTAS.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:28:59.605636+00:00
-- url     : https://prove2.me/theorems/9f591e39-e520-4952-afba-14d3c40aff24
-- title:
--   Theorem 1.1, p.6 (corrected: the grids and the empty output of the single-nest step) — the FPTAS
-- statement:
--   There is a universal constant $K$ such that the program `fptas` has the following guarantees for every accuracy level $\epsilon>0$.
--
--   1. For every instance, if a $\mathcal C$-feasible assortment exists, then the program returns an assortment.
--   2. For every instance, every assortment $\tilde S$ it returns is $\mathcal C$-feasible, and
--   $$
--   \mathcal R(\tilde S)\ge(1-\epsilon)\cdot\mathcal R(S)\quad\text{for every }\mathcal C\text{-feasible assortment }S.
--   $$
--   3. For every rational instance, the number of operations is at most
--   $$
--   K\cdot\mathrm{inputSize}^{20}\cdot\max(1,1/\epsilon)^8\cdot\Big(\frac{\gamma^+}{\gamma^-}\Big)^{10},
--   $$
--   where $\gamma^+=\max\{1,\gamma_1,\dots,\gamma_M\}$ and $\gamma^-=\min\{1,\gamma_1,\dots,\gamma_M\}$.
--
--   This is the paper's main result: capacitated assortment optimization under the Nested Logit model can be approximated within $1-\epsilon$ in its full generality, with dissimilarity parameters above $1$ and nest-level no-purchase weights, in time polynomial in the input size, $1/\epsilon$ and $\gamma^+/\gamma^-$.
--
--   Differences from the source:
--   - encoding: products in pairwise-disjoint nests N₁, …, N_M; assortments S = (S₁, …, S_M); non-negative γₘ → Fin n with nest : Fin n → Fin M; S : Finset (Fin n) with Sₘ = part S m; 0 < M, nonempty nests, 0 < γₘ; reason: same instances wherever the paper is defined: at γₘ = 0 the ratio γ⁺/γ⁻ and the power ωₖ^{1/γₖ} are undefined, and W↓, r_min, π_min minimize over Nₘ
--   - generalization: signs of c, C, w₀ are not stated; w₀ read as a positive weight → c and C real of any sign, w₀ ≥ 0, w₀ₘ ≥ 0; R(∅) = 0 at w₀ = 0; reason: the proofs use no sign of c or C, and every instance with nonnegative costs and positive w₀ is covered
--   - generalization: the instance data are the "input" of a polynomial-time algorithm → the accuracy clauses hold for real data; the operation count is stated for rational data of the given bit length; reason: rational instances are a special case of the accuracy clauses
--   - encoding: any ϵ > 0 in the parameters ξω, ξρ, δω, δρ → the program uses ϵ̂ = min(ϵ, 1) in all its parameters; reason: no change for ϵ ≤ 1; the parameters need ϵ ≤ 80 and for ϵ ≥ 1 the guarantee is empty
--   - correction: Dω with p ≤ γ⁺·log_{1+ξω}(W↑/W↓); Dρ from π_min r_min W↓^{γ⁺} with q ≤ γ⁺·log_{1+ξρ}((r_max/(π_min r_min))(W↑/W↓)) → Pω = ⌈(γ⁺ log(W↑/W↓) + log M)/log(1+ξω)⌉ + M + 1; Lρ = (1−ξρ)^M π_min r_min W↓^{γ⁺}; Qρ = ⌈log(M r_max W↑^{γ⁺}/Lρ)/log(1+ξρ)⌉; reason: the printed tops cover one nest but the states hold sums: M = 2, one product per nest, r = w = c = 1, γ = 1, w₀ₘ = 0, w₀ = 2, C = 2 gives Dω = Dρ = {0, 1}, so R(S̃) ≤ 1/3 < (1−ϵ)/2 for ϵ < 1/3; and the printed bottom rounds (1−ξρ)·1 down to 0 there, so A(1, ω*₁, 0) = ∞ > c(S₁)
--   - correction: G over all subsets S ⊆ {1, …, t}; the search may return ∅ → the search reads G over nonempty subsets (an extra table); the recursion starts at t = 0; reason: one product with w = 0.05, r = 12, c = 1, w₀ₖ = 1, γₖ = 1, ωₖ = ρₖ = 1, δρ = 1/2, δω = 1/16: the neighbourhood is nonempty, but (η, ζ) = (0, 0) has G = 0, and ∅ is outside N_(2δω,20δρ)
--   - reading: Rₖ(T) ∈ (1 ± δρ)·ρₖ/w₊(T)^{γₖ}, undefined at T = ∅ → Rₖ(T)·w₊(T)^{γₖ} ∈ (1 ± δρ)·ρₖ, and ∅ is a member exactly when ωₖ = ρₖ = 0; reason: §4.1 calls the zero cases trivial; this agrees with (P₂), (P₃), and Lean's x/0 = 0 would put ∅ in N(k, 0, ρₖ) for ρₖ > 0
--   - reading: running time of "our algorithm", no machine model; arithmetic operations and table accesses are counted in §3.4, §4.2 → operations charged in the instrumented program: unit-cost +, −, ×, /, ≤, ⌊·⌋, ⌈·⌉, Real.rpow, Real.log and array accesses; reason: exact w₊^γ is irrational for rational data, so this is the accounting the paper performs
--   - reading: "can be approximated within factor 1 − ϵ of optimal"; "the running time of our algorithm" → a statement about the explicit program fptas, with one constant K before all the data, and with an exponent 20 obtained from n³M⁷L_w⁶L_r⁴; reason: without the program the accuracy claim holds trivially, by taking the optimum itself
-- source:
--   Segev, Approximation Schemes for Capacity-Constrained Assortment Optimization under the Nested Logit Model, SSRN #3553264 (Mar 2020), Theorem 1.1, p.6

import Mathlib
import Definitions.Def_NestedLogitFPTAS_Model
import Definitions.Def_NestedLogitFPTAS_Grids
import Definitions.Def_NestedLogitFPTAS_Program
import Definitions.Def_NestedLogitFPTAS_Rational

namespace NestedLogitFPTAS

/-- Segev, SSRN #3553264 (Mar 2020), Theorem 1.1, p.6 (**corrected** in the printed grids and the empty output
of the single-nest algorithm): for every accuracy level `ϵ > 0`, the program `fptas` returns a
`C`-feasible assortment whenever one exists, whatever it returns has revenue at least `(1 - ϵ)` times
that of every `C`-feasible assortment, and on rational instances it uses at most
`K·inputSize²⁰·max(1, 1/ϵ)⁸·(γ⁺/γ⁻)¹⁰` operations, with one universal constant `K`.

**Formalization Note.** The statement is about the explicit program: without it the claim would hold
by taking the optimum itself. The "running time" counts unit-cost arithmetic operations, comparisons,
`Real.rpow`, `Real.log` and array accesses, as the paper does in §3.4 and §4.2. Accuracy holds for real
data. `K` is quantified before all the data. -/
theorem theorem_1_1 :
    ∃ K : ℝ, 0 < K ∧
      (∀ {n M : ℕ} (I : Instance n M), I.Standing → ∀ ε : ℝ, 0 < ε →
        ((∃ S, I.Feasible S) → ∃ S', I.output ε = some S') ∧
        (∀ S', I.output ε = some S' →
          I.Feasible S' ∧ ∀ S, I.Feasible S → (1 - ε) * I.R S ≤ I.R S')) ∧
      (∀ {n M : ℕ} (J : RatInstance n M), J.toReal.Standing → ∀ ε : ℝ, 0 < ε →
        (J.toReal.ops ε : ℝ) ≤
          K * (J.inputSize : ℝ) ^ 20 * (max 1 (1 / ε)) ^ 8 *
            (J.toReal.gammaPlus / J.toReal.gammaMinus) ^ 10) := by sorry

end NestedLogitFPTAS
