-- Prove2me | Theorems.Thm_LimitedEntanglementTomography_LowerBound_corollary_4_18
-- name    : LimitedEntanglementTomography.LowerBound.corollary_4_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:12:34.707541+00:00
-- url     : https://prove2.me/theorems/f7bd466a-f0be-489f-a2d6-dcd57360a8d2
-- title:
--   Corollary 4.18 — $\Pr[\|Z\|_{\mathrm{op}}\ge 8\sqrt d]\le 2e^{-(8-2\log 9)d}\le 1/10$
-- statement:
--   Let $Z$ be a standard Gaussian on $\mathrm{Herm}_0(\mathbb C^d)$ with the Frobenius inner product. For all sufficiently large $d$,
--   $$\Pr\big[\|Z\|_{\mathrm{op}}\ge 8\sqrt d\,\big]\le 2\exp\big(-(8-2\log 9)\,d\big)\le\frac1{10}.$$
--
--   This operator-norm tail is the input to the bound (46) of Lemma 6.3, which controls the mass of the truncation set of the prior.
--
--   Differences from the source:
--   - encoding: one fixed Frobenius-orthonormal basis F_1,…,F_{d²−1} of Herm₀(ℂ^d) → the statement holds for every orthonormal basis F (IsHerm0ONB F); reason: the source fixes an arbitrary such basis, so its claim is the same claim for every basis; trace Fisher information and the standard Gaussian law do not depend on the basis
--   - encoding: random matrices and sets in Herm₀(ℂ^d) → coordinates θ ∈ ℝ^{d²−1} with Δ = ∑_b θ_b F_b (herm0Coord); reason: an isometric linear bijection for the Frobenius norm; laws and events correspond one to one
--   - encoding: probabilities and expectations of nonnegative quantities in ℝ → values of measures in [0,∞] (ENNReal); reason: a probability is the same number; inequalities are unchanged
-- source:
--   Ufuk Keskin, Jason Luo, Mahbod Majid, Matthew Radzihovsky, Tight Lower Bounds for State Tomography with Limited Entanglement, STOC 2027 submission #1625 (October 2026), source.pdf SHA-256 bdd8884c95899a0c563507d1c005e0dee86e418d52478a2e9e6682bb1f9d29c3, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1625.pdf, §4.5, printed p.18 / PDF p.20, Corollary 4.18 (eq. (34))

import Mathlib
import Definitions.Def_LimitedEntanglementTomography_LowerBound_Prior

open scoped ENNReal ComplexOrder

/-!
Ufuk Keskin, Jason Luo, Mahbod Majid, Matthew Radzihovsky, *Tight Lower Bounds for State
Tomography with Limited Entanglement*, STOC 2027 submission #1625 (October 2026), Corollary 4.18, printed p.18 / PDF p.20, eq. (34).
-/

namespace LimitedEntanglementTomography.LowerBound

open MeasureTheory ProbabilityTheory Matrix ShadowTomography.ClassicalLB

/-- **Corollary 4.18.** Let `Z` be a standard Gaussian on `Herm₀(ℂ^d)` with the Frobenius inner
product (`Z = ∑_b θ_b F_b` with `θ` standard Gaussian on `ℝ^{d²−1}` and `F` an orthonormal basis).
For all sufficiently large `d`,
`Pr[‖Z‖_op ≥ 8√d] ≤ 2 exp(−(8 − 2 log 9) d) ≤ 1/10`. -/
theorem corollary_4_18 :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ F : Fin (d ^ 2 - 1) → Op d, IsHerm0ONB F →
      stdGauss (d ^ 2 - 1) {θ | 8 * Real.sqrt d ≤ opNorm (herm0Coord F θ)} ≤
          ENNReal.ofReal (2 * Real.exp (-((8 - 2 * Real.log 9) * d))) ∧
        2 * Real.exp (-((8 - 2 * Real.log 9) * d)) ≤ 1 / 10 := by sorry

end LimitedEntanglementTomography.LowerBound
