-- Prove2me | Theorems.Thm_NestedLogitFPTAS_lemma_3_5
-- name    : NestedLogitFPTAS.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:28:41.329845+00:00
-- url     : https://prove2.me/theorems/8f10a097-7461-474d-b9b6-a976d44f8acc
-- title:
--   Lemma 3.5, p.16 (corrected: grids $\mathcal D_\omega$, $\mathcal D_\rho$) — the rounded ratio is close to the revenue
-- statement:
--   Let $\epsilon>0$ and let $S$ be an assortment. For $\omega^*=\langle(1+\xi_\omega)^M\omega_{[1,M]}(S)\rangle_{\mathcal D_\omega}$ and $\rho^*=\langle(1-\xi_\rho)^M\rho_{[1,M]}(S)\rangle_{\mathcal D_\rho}$,
--   $$
--   \frac{\rho^*}{w_0+\omega^*}\ge\Big(1-\frac\epsilon2\Big)\cdot\mathcal R(S).
--   $$
--   Rounding the two sums therefore loses little revenue.
--
--   Differences from the source:
--   - encoding: products in pairwise-disjoint nests N₁, …, N_M; assortments S = (S₁, …, S_M); non-negative γₘ → Fin n with nest : Fin n → Fin M; S : Finset (Fin n) with Sₘ = part S m; 0 < M, nonempty nests, 0 < γₘ; reason: same instances wherever the paper is defined: at γₘ = 0 the ratio γ⁺/γ⁻ and the power ωₖ^{1/γₖ} are undefined, and W↓, r_min, π_min minimize over Nₘ
--   - encoding: any ϵ > 0 in the parameters ξω, ξρ, δω, δρ → the program uses ϵ̂ = min(ϵ, 1) in all its parameters; reason: no change for ϵ ≤ 1; the parameters need ϵ ≤ 80 and for ϵ ≥ 1 the guarantee is empty
--   - correction: Dω with p ≤ γ⁺·log_{1+ξω}(W↑/W↓); Dρ from π_min r_min W↓^{γ⁺} with q ≤ γ⁺·log_{1+ξρ}((r_max/(π_min r_min))(W↑/W↓)) → Pω = ⌈(γ⁺ log(W↑/W↓) + log M)/log(1+ξω)⌉ + M + 1; Lρ = (1−ξρ)^M π_min r_min W↓^{γ⁺}; Qρ = ⌈log(M r_max W↑^{γ⁺}/Lρ)/log(1+ξρ)⌉; reason: the printed tops cover one nest but the states hold sums: M = 2, one product per nest, r = w = c = 1, γ = 1, w₀ₘ = 0, w₀ = 2, C = 2 gives Dω = Dρ = {0, 1}, so R(S̃) ≤ 1/3 < (1−ϵ)/2 for ϵ < 1/3; and the printed bottom rounds (1−ξρ)·1 down to 0 there, so A(1, ω*₁, 0) = ∞ > c(S₁)
--   - generalization: S an optimal dual assortment, with R(S*) on the right → every assortment S, with R(S) on the right; reason: the proof uses only the two rounded sums, and R(S) = R(S*) comes from Lemma 2.1
--   - generalization: signs of c, C, w₀ are not stated; w₀ read as a positive weight → c and C real of any sign, w₀ ≥ 0, w₀ₘ ≥ 0; R(∅) = 0 at w₀ = 0; reason: the proofs use no sign of c or C, and every instance with nonnegative costs and positive w₀ is covered
-- source:
--   Segev, Approximation Schemes for Capacity-Constrained Assortment Optimization under the Nested Logit Model, SSRN #3553264 (Mar 2020), Lemma 3.5, p.16; proof in Appendix A.1

import Mathlib
import Definitions.Def_NestedLogitFPTAS_Model
import Definitions.Def_NestedLogitFPTAS_Grids
import Definitions.Def_NestedLogitFPTAS_RoundedPath

namespace NestedLogitFPTAS

/-- Segev, SSRN #3553264 (Mar 2020), Lemma 3.5, p.16 (proof in Appendix A.1): for
`ω* = ⟨(1+ξω)^M·ω[1,M](S)⟩_{Dω}` and `ρ* = ⟨(1-ξρ)^M·ρ[1,M](S)⟩_{Dρ}`,
`ρ*/(w₀ + ω*) ≥ (1 - ϵ/2)·R(S)`.

**Formalization Note.** The paper's `S` is a dual optimum with `R(S) = R(S*)`; the lemma holds for
every assortment, with `R(S)` on the right. `ω*`, `ρ*` are `omegaStarAbove`, `rhoStarAbove` at index
`0`. -/
theorem lemma_3_5 {n M : ℕ} (I : Instance n M) (hI : I.Standing) {ε : ℝ} (hε : 0 < ε)
    (S : Finset (Fin n)) :
    (1 - ε / 2) * I.R S ≤ I.rhoStarAbove ε S 0 / (I.w0 + I.omegaStarAbove ε S 0) := by sorry

end NestedLogitFPTAS
