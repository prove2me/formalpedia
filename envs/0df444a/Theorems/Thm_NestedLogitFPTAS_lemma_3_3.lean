-- Prove2me | Theorems.Thm_NestedLogitFPTAS_lemma_3_3
-- name    : NestedLogitFPTAS.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:28:39.299927+00:00
-- url     : https://prove2.me/theorems/d1597026-2ee2-4d9a-967d-08e79b07f80c
-- title:
--   Lemma 3.3, p.14 (corrected: grids $\mathcal D_\omega$, $\mathcal D_\rho$) — $\mathcal R(\tilde S)\ge(1-\epsilon/2)\cdot\tilde\rho/(w_0+\tilde\omega)$
-- statement:
--   Let $\epsilon>0$, $\hat\epsilon=\min(\epsilon,1)$, and let $\tilde S$ be the output of the program with selected pair $(\tilde\omega,\tilde\rho)$. Then
--   $$
--   \omega_{[1,M]}(\tilde S)\le\Big(1+\frac{\hat\epsilon}4\Big)\tilde\omega,\qquad \rho_{[1,M]}(\tilde S)\ge\Big(1-\frac{\hat\epsilon}4\Big)\tilde\rho,
--   $$
--   and consequently
--   $$
--   \mathcal R(\tilde S)\ge\Big(1-\frac{\hat\epsilon}2\Big)\cdot\frac{\tilde\rho}{w_0+\tilde\omega}.
--   $$
--   So what the program claims about its output is nearly true of it.
--
--   Differences from the source:
--   - encoding: products in pairwise-disjoint nests N₁, …, N_M; assortments S = (S₁, …, S_M); non-negative γₘ → Fin n with nest : Fin n → Fin M; S : Finset (Fin n) with Sₘ = part S m; 0 < M, nonempty nests, 0 < γₘ; reason: same instances wherever the paper is defined: at γₘ = 0 the ratio γ⁺/γ⁻ and the power ωₖ^{1/γₖ} are undefined, and W↓, r_min, π_min minimize over Nₘ
--   - generalization: signs of c, C, w₀ are not stated; w₀ read as a positive weight → c and C real of any sign, w₀ ≥ 0, w₀ₘ ≥ 0; R(∅) = 0 at w₀ = 0; reason: the proofs use no sign of c or C, and every instance with nonnegative costs and positive w₀ is covered
--   - encoding: any ϵ > 0 in the parameters ξω, ξρ, δω, δρ → the program uses ϵ̂ = min(ϵ, 1) in all its parameters; reason: no change for ϵ ≤ 1; the parameters need ϵ ≤ 80 and for ϵ ≥ 1 the guarantee is empty
--   - correction: Dω with p ≤ γ⁺·log_{1+ξω}(W↑/W↓); Dρ from π_min r_min W↓^{γ⁺} with q ≤ γ⁺·log_{1+ξρ}((r_max/(π_min r_min))(W↑/W↓)) → Pω = ⌈(γ⁺ log(W↑/W↓) + log M)/log(1+ξω)⌉ + M + 1; Lρ = (1−ξρ)^M π_min r_min W↓^{γ⁺}; Qρ = ⌈log(M r_max W↑^{γ⁺}/Lρ)/log(1+ξρ)⌉; reason: the printed tops cover one nest but the states hold sums: M = 2, one product per nest, r = w = c = 1, γ = 1, w₀ₘ = 0, w₀ = 2, C = 2 gives Dω = Dρ = {0, 1}, so R(S̃) ≤ 1/3 < (1−ϵ)/2 for ϵ < 1/3; and the printed bottom rounds (1−ξρ)·1 down to 0 there, so A(1, ω*₁, 0) = ∞ > c(S₁)
--   - correction: G over all subsets S ⊆ {1, …, t}; the search may return ∅ → the search reads G over nonempty subsets (an extra table); the recursion starts at t = 0; reason: one product with w = 0.05, r = 12, c = 1, w₀ₖ = 1, γₖ = 1, ωₖ = ρₖ = 1, δρ = 1/2, δω = 1/16: the neighbourhood is nonempty, but (η, ζ) = (0, 0) has G = 0, and ∅ is outside N_(2δω,20δρ)
-- source:
--   Segev, Approximation Schemes for Capacity-Constrained Assortment Optimization under the Nested Logit Model, SSRN #3553264 (Mar 2020), Lemma 3.3, p.14; proof in §3.6, pp.15–16

import Mathlib
import Definitions.Def_NestedLogitFPTAS_Model
import Definitions.Def_NestedLogitFPTAS_Grids
import Definitions.Def_NestedLogitFPTAS_Program

namespace NestedLogitFPTAS

/-- Segev, SSRN #3553264 (Mar 2020), Lemma 3.3, p.14 (proof in §3.6, pp.15–16), with its two items:
`ω[1,M](S̃) ≤ (1 + ϵ/4)·ω̃`, `ρ[1,M](S̃) ≥ (1 - ϵ/4)·ρ̃`, and `R(S̃) ≥ (1 - ϵ/2)·ρ̃/(w₀ + ω̃)`.

**Formalization Note.** All three are stated with `ϵ̂ = min(ϵ, 1)`, which is the paper's `ϵ` for
`ϵ ≤ 1` and implies the `ϵ` form for larger `ϵ`. -/
theorem lemma_3_3 {n M : ℕ} (I : Instance n M) (hI : I.Standing) {ε : ℝ} (hε : 0 < ε)
    {S' : Finset (Fin n)} {p q : ℕ} (hS' : I.output ε = some S')
    (hsel : I.selected ε = some (p, q)) :
    I.omegaRange 1 M S' ≤ (1 + epsHat ε / 4) * I.omegaAt ε p ∧
      (1 - epsHat ε / 4) * I.rhoAt ε q ≤ I.rhoRange 1 M S' ∧
      (1 - epsHat ε / 2) * (I.rhoAt ε q / (I.w0 + I.omegaAt ε p)) ≤ I.R S' := by sorry

end NestedLogitFPTAS
