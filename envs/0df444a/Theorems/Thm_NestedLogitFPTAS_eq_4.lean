-- Prove2me | Theorems.Thm_NestedLogitFPTAS_eq_4
-- name    : NestedLogitFPTAS.eq_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:28:41.006386+00:00
-- url     : https://prove2.me/theorems/0990f517-d3a7-45ca-86ee-cc029a026d36
-- title:
--   Eq. (4), p.13 (corrected: grids $\mathcal D_\omega$, $\mathcal D_\rho$) — the table of $\tilde F$ satisfies the recursion
-- statement:
--   Let $\epsilon>0$. The table computed by the program satisfies $\tilde F(M+1,0,0)=0$ and $\tilde F(M+1,\omega,\rho)=\infty$ for $(0,0)\neq(\omega,\rho)\in\mathcal D_\omega\times\mathcal D_\rho$, and for every $k\le M$ and $(\omega,\rho)\in\mathcal D_\omega\times\mathcal D_\rho$,
--   $$
--   \tilde F(k,\omega,\rho)=\min_{\substack{\omega_k,\omega_{>k}\in\mathcal D_\omega,\ \rho_k,\rho_{>k}\in\mathcal D_\rho\\ \omega_k+\omega_{>k}\le\omega,\ \rho_k+\rho_{>k}\ge\rho}}\mathcal A(k,\omega_k,\rho_k)+\tilde F(k+1,\omega_{>k},\rho_{>k}).
--   $$
--   This identifies the imperative table with the recursion on which the whole analysis is based.
--
--   **Formalization Note** States are grid indices (`omegaAt p`, `rhoAt q`), and nest index $k$ is the paper's $k+1$. An empty minimum is $\infty$.
--
--   Differences from the source:
--   - encoding: products in pairwise-disjoint nests N₁, …, N_M; assortments S = (S₁, …, S_M); non-negative γₘ → Fin n with nest : Fin n → Fin M; S : Finset (Fin n) with Sₘ = part S m; 0 < M, nonempty nests, 0 < γₘ; reason: same instances wherever the paper is defined: at γₘ = 0 the ratio γ⁺/γ⁻ and the power ωₖ^{1/γₖ} are undefined, and W↓, r_min, π_min minimize over Nₘ
--   - generalization: signs of c, C, w₀ are not stated; w₀ read as a positive weight → c and C real of any sign, w₀ ≥ 0, w₀ₘ ≥ 0; R(∅) = 0 at w₀ = 0; reason: the proofs use no sign of c or C, and every instance with nonnegative costs and positive w₀ is covered
--   - encoding: any ϵ > 0 in the parameters ξω, ξρ, δω, δρ → the program uses ϵ̂ = min(ϵ, 1) in all its parameters; reason: no change for ϵ ≤ 1; the parameters need ϵ ≤ 80 and for ϵ ≥ 1 the guarantee is empty
--   - correction: Dω with p ≤ γ⁺·log_{1+ξω}(W↑/W↓); Dρ from π_min r_min W↓^{γ⁺} with q ≤ γ⁺·log_{1+ξρ}((r_max/(π_min r_min))(W↑/W↓)) → Pω = ⌈(γ⁺ log(W↑/W↓) + log M)/log(1+ξω)⌉ + M + 1; Lρ = (1−ξρ)^M π_min r_min W↓^{γ⁺}; Qρ = ⌈log(M r_max W↑^{γ⁺}/Lρ)/log(1+ξρ)⌉; reason: the printed tops cover one nest but the states hold sums: M = 2, one product per nest, r = w = c = 1, γ = 1, w₀ₘ = 0, w₀ = 2, C = 2 gives Dω = Dρ = {0, 1}, so R(S̃) ≤ 1/3 < (1−ϵ)/2 for ϵ < 1/3; and the printed bottom rounds (1−ξρ)·1 down to 0 there, so A(1, ω*₁, 0) = ∞ > c(S₁)
--   - correction: G over all subsets S ⊆ {1, …, t}; the search may return ∅ → the search reads G over nonempty subsets (an extra table); the recursion starts at t = 0; reason: one product with w = 0.05, r = 12, c = 1, w₀ₖ = 1, γₖ = 1, ωₖ = ρₖ = 1, δρ = 1/2, δω = 1/16: the neighbourhood is nonempty, but (η, ζ) = (0, 0) has G = 0, and ∅ is outside N_(2δω,20δρ)
-- source:
--   Segev, Approximation Schemes for Capacity-Constrained Assortment Optimization under the Nested Logit Model, SSRN #3553264 (Mar 2020), §3.4, eq. (4), p.13

import Mathlib
import Definitions.Def_NestedLogitFPTAS_Model
import Definitions.Def_NestedLogitFPTAS_Grids
import Definitions.Def_NestedLogitFPTAS_SingleNest
import Definitions.Def_NestedLogitFPTAS_Program

open Classical

namespace NestedLogitFPTAS

/-- Segev, SSRN #3553264 (Mar 2020), eq. (4) and the terminal states, p.13: the table of `F̃` computed by the
program satisfies `F̃(M+1, 0, 0) = 0`, `F̃(M+1, ω, ρ) = ∞` for `(0,0) ≠ (ω,ρ) ∈ Dω × Dρ`, and for
`k ≤ M`, `F̃(k, ω, ρ)` is the minimum of `A(k, ωk, ρk) + F̃(k+1, ω>k, ρ>k)` over
`ωk, ω>k ∈ Dω`, `ρk, ρ>k ∈ Dρ` with `ωk + ω>k ≤ ω` and `ρk + ρ>k ≥ ρ`.

**Formalization Note.** States are grid indices: the grids are corrected, `Ftilde ε k` is the paper's
`k + 1`, and `Ftilde ε M` is the terminal row. The minimum is a `WithTop ℝ` infimum, `⊤` over the empty
set. `A` runs at `δω = ϵ̂/(640γ⁺)`, `δρ = ϵ̂/80`, p.13. -/
theorem eq_4 {n M : ℕ} (I : Instance n M) (hI : I.Standing) {ε : ℝ} (hε : 0 < ε) :
    (∀ p q, p < I.Pomega ε + 2 → q < I.Qrho ε + 2 →
      I.Ftilde ε M p q = if p = 0 ∧ q = 0 then 0 else ⊤) ∧
    (∀ (k : Fin M) (p q : ℕ), p < I.Pomega ε + 2 → q < I.Qrho ε + 2 →
      I.Ftilde ε k p q =
        (((Finset.range (I.Pomega ε + 2) ×ˢ Finset.range (I.Pomega ε + 2)) ×ˢ
            (Finset.range (I.Qrho ε + 2) ×ˢ Finset.range (I.Qrho ε + 2))).filter
          (fun x => I.omegaAt ε x.1.1 + I.omegaAt ε x.1.2 ≤ I.omegaAt ε p ∧
            I.rhoAt ε q ≤ I.rhoAt ε x.2.1 + I.rhoAt ε x.2.2)).inf
          (fun x => I.Acost (I.deltaOmega ε) (I.deltaRho ε) k
              (I.omegaAt ε x.1.1) (I.rhoAt ε x.2.1) +
            I.Ftilde ε (k.val + 1) x.1.2 x.2.2)) := by sorry

end NestedLogitFPTAS
