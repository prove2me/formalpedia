-- Prove2me | Theorems.Thm_NestedLogitFPTAS_lemma_4_3
-- name    : NestedLogitFPTAS.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:27:52.418061+00:00
-- url     : https://prove2.me/theorems/62b218a6-09af-45d0-abcf-cc2332c9d15c
-- title:
--   Lemma 4.3, p.19 (corrected: $G$ over nonempty subsets) — the search intervals contain a state of cost at most $\mathcal P_\approx$
-- statement:
--   Let $\delta_\rho\in(0,1]$, $\delta_\omega\in(0,\delta_\rho/(8\gamma^+)]$ and $\omega_k,\rho_k>0$. If $\mathcal N_{(\delta_\omega,\delta_\rho)}(k,\omega_k,\rho_k)\neq\emptyset$, there are integer multiples
--   $$
--   \eta\in\Big[\frac{(1-2\delta_\omega)\omega_k^{1/\gamma_k}-w_{0k}}{w_{\rm base}},\frac{(1+\delta_\omega)\omega_k^{1/\gamma_k}-w_{0k}}{w_{\rm base}}\Big],\quad
--   \zeta\in\Big[\frac{(1-3\delta_\rho)\rho_k}{\lambda_{\rm base}\,\omega_k^{1-1/\gamma_k}},\frac{(1+3\delta_\rho)\rho_k}{\lambda_{\rm base}\,\omega_k^{1-1/\gamma_k}}\Big]
--   $$
--   with $\eta\le\lceil2|N_k|/\delta_\omega\rceil$, $\zeta\le\lceil4|N_k|/\delta_\rho\rceil$ and
--   $$
--   G(|N_k|,\eta,\zeta)\le\mathcal P_{\approx(\delta_\omega,\delta_\rho)}(k,\omega_k,\rho_k).
--   $$
--   So the final search of the algorithm finds a set at least as cheap as any set of the neighbourhood.
--
--   Differences from the source:
--   - encoding: products in pairwise-disjoint nests N₁, …, N_M; assortments S = (S₁, …, S_M); non-negative γₘ → Fin n with nest : Fin n → Fin M; S : Finset (Fin n) with Sₘ = part S m; 0 < M, nonempty nests, 0 < γₘ; reason: same instances wherever the paper is defined: at γₘ = 0 the ratio γ⁺/γ⁻ and the power ωₖ^{1/γₖ} are undefined, and W↓, r_min, π_min minimize over Nₘ
--   - reading: Rₖ(T) ∈ (1 ± δρ)·ρₖ/w₊(T)^{γₖ}, undefined at T = ∅ → Rₖ(T)·w₊(T)^{γₖ} ∈ (1 ± δρ)·ρₖ, and ∅ is a member exactly when ωₖ = ρₖ = 0; reason: §4.1 calls the zero cases trivial; this agrees with (P₂), (P₃), and Lean's x/0 = 0 would put ∅ in N(k, 0, ρₖ) for ρₖ > 0
--   - correction: G over all subsets S ⊆ {1, …, t}; the search may return ∅ → the search reads G over nonempty subsets (an extra table); the recursion starts at t = 0; reason: one product with w = 0.05, r = 12, c = 1, w₀ₖ = 1, γₖ = 1, ωₖ = ρₖ = 1, δρ = 1/2, δω = 1/16: the neighbourhood is nonempty, but (η, ζ) = (0, 0) has G = 0, and ∅ is outside N_(2δω,20δρ)
-- source:
--   Segev, Approximation Schemes for Capacity-Constrained Assortment Optimization under the Nested Logit Model, SSRN #3553264 (Mar 2020), Lemma 4.3, p.19; proof in Appendix A.5

import Mathlib
import Definitions.Def_NestedLogitFPTAS_Model
import Definitions.Def_NestedLogitFPTAS_Neighbourhood
import Definitions.Def_NestedLogitFPTAS_SingleNest

namespace NestedLogitFPTAS

/-- Segev, SSRN #3553264 (Mar 2020), Lemma 4.3, p.19 (proof in Appendix A.5): when the neighbourhood is
nonempty, there are integer multiples `η`, `ζ` in the two search intervals with
`G(|Nₖ|, η, ζ) ≤ P≈_(δω,δρ)(k, ωk, ρk)`.

**Formalization Note.** The conclusion includes what the proof adds, p.19: `η` and `ζ` reside in the
state space. `G` is taken over nonempty subsets, and this loses nothing, because `ωk > 0` forces the
sets of the neighbourhood to be nonempty. -/
theorem lemma_4_3 {n M : ℕ} (I : Instance n M) (hI : I.Standing) {δω δρ ωk ρk : ℝ} (k : Fin M)
    (hδρ : 0 < δρ) (hδρ1 : δρ ≤ 1) (hδω : 0 < δω)
    (hδω' : δω ≤ δρ / (8 * I.gammaPlus))
    (hωk : 0 < ωk) (hρk : 0 < ρk) (hN : (I.Nbhd δω δρ k ωk ρk).Nonempty) :
    ∃ η ζ : ℕ,
      ((1 - 2 * δω) * ωk ^ (1 / I.γ k) - I.w0n k) / I.wBase δω k ωk ≤ (η : ℝ) ∧
      (η : ℝ) ≤ ((1 + δω) * ωk ^ (1 / I.γ k) - I.w0n k) / I.wBase δω k ωk ∧
      (1 - 3 * δρ) * ρk / (I.lamBase δρ k ωk ρk * ωk ^ (1 - 1 / I.γ k)) ≤ (ζ : ℝ) ∧
      (ζ : ℝ) ≤ (1 + 3 * δρ) * ρk / (I.lamBase δρ k ωk ρk * ωk ^ (1 - 1 / I.γ k)) ∧
      η ≤ ⌈2 * ((I.nestSet k).card : ℝ) / δω⌉₊ ∧
      ζ ≤ ⌈4 * ((I.nestSet k).card : ℝ) / δρ⌉₊ ∧
      I.GN δω δρ k ωk ρk η ζ ≤ I.Papprox δω δρ k ωk ρk := by sorry

end NestedLogitFPTAS
