-- Prove2me | Theorems.Thm_LimitedEntanglementTomography_LowerBound_lemma_6_4
-- name    : LimitedEntanglementTomography.LowerBound.lemma_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:12:47.60078+00:00
-- url     : https://prove2.me/theorems/ec080ae3-b974-46e4-a523-b0498ceb6e34
-- title:
--   Lemma 6.4 — $\Pr[\|Z\|_1\le \tfrac{c_0}2 d^{3/2}]\le e^{-a_0d^2}$
-- statement:
--   Let $C_0,c_0>0$ and $d_0$ be constants as in Lemma 6.3, that is, such that (46), (47) and (48) hold for every $d\ge d_0$. There is an absolute constant $a_0>0$ such that, for every $d\ge d_0$ and the standard Gaussian $Z$ on $\mathrm{Herm}_0(\mathbb C^d)$,
--   $$\Pr\Big[\|Z\|_1\le\frac{c_0}2\,d^{3/2}\Big]\le e^{-a_0d^2}.$$
--
--   This lower tail, combined with Anderson's inequality, makes every trace-norm ball of radius $2\varepsilon$ exponentially unlikely under the prior.
--
--   Differences from the source:
--   - reading: "Let c₀, d₀ be as in Lemma 6.3" → C₀, c₀ > 0 and d₀ are arbitrary constants satisfying the three conclusions (46)–(48) of Lemma 6.3 for every d ≥ d₀ (hypothesis h63); reason: this is what "as in Lemma 6.3" refers to; with Lemma 6.3 (which asserts such constants exist) it gives the source statement, and it states the claim for every admissible choice
--   - encoding: one fixed Frobenius-orthonormal basis F_1,…,F_{d²−1} of Herm₀(ℂ^d) → the statement holds for every orthonormal basis F (IsHerm0ONB F); reason: the source fixes an arbitrary such basis, so its claim is the same claim for every basis; trace Fisher information and the standard Gaussian law do not depend on the basis
--   - encoding: random matrices and sets in Herm₀(ℂ^d) → coordinates θ ∈ ℝ^{d²−1} with Δ = ∑_b θ_b F_b (herm0Coord); reason: an isometric linear bijection for the Frobenius norm; laws and events correspond one to one
--   - encoding: probabilities and expectations of nonnegative quantities in ℝ → values of measures in [0,∞] (ENNReal); reason: a probability is the same number; inequalities are unchanged
-- source:
--   Ufuk Keskin, Jason Luo, Mahbod Majid, Matthew Radzihovsky, Tight Lower Bounds for State Tomography with Limited Entanglement, STOC 2027 submission #1625 (October 2026), source.pdf SHA-256 bdd8884c95899a0c563507d1c005e0dee86e418d52478a2e9e6682bb1f9d29c3, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1625.pdf, §6, printed p.24 / PDF p.26, Lemma 6.4 (eq. (49))

import Mathlib
import Definitions.Def_LimitedEntanglementTomography_LowerBound_Prior

open scoped ENNReal ComplexOrder

/-!
Ufuk Keskin, Jason Luo, Mahbod Majid, Matthew Radzihovsky, *Tight Lower Bounds for State
Tomography with Limited Entanglement*, STOC 2027 submission #1625 (October 2026), Lemma 6.4, printed p.24 / PDF p.26, eq. (49).
-/

namespace LimitedEntanglementTomography.LowerBound

open MeasureTheory ProbabilityTheory Matrix ShadowTomography.ClassicalLB

/-- **Lemma 6.4.** Let `C₀, c₀ > 0` and `d₀` be constants as in Lemma 6.3 (that is, satisfying
(46)–(48) for every `d ≥ d₀`). There is an absolute constant `a₀ > 0` such that for every
`d ≥ d₀` and the standard Gaussian `Z` on `Herm₀(ℂ^d)`,
`Pr[‖Z‖₁ ≤ (c₀/2) d^{3/2}] ≤ e^{−a₀ d²}`. -/
theorem lemma_6_4 (C₀ c₀ : ℝ) (d₀ : ℕ) (hC₀ : 0 < C₀) (hc₀ : 0 < c₀)
    (h63 : ∀ d : ℕ, d₀ ≤ d → ∀ F : Fin (d ^ 2 - 1) → Op d, IsHerm0ONB F →
      ENNReal.ofReal (9 / 10) ≤
          stdGauss (d ^ 2 - 1) {θ | opNorm (herm0Coord F θ) ≤ C₀ * Real.sqrt d} ∧
      ENNReal.ofReal (9 / 10) ≤
          stdGauss (d ^ 2 - 1) {θ | ((d : ℝ) ^ 2 - 1) / 2 ≤ frobNorm (herm0Coord F θ) ^ 2} ∧
      c₀ * (d : ℝ) ^ ((3 : ℝ) / 2) ≤ ∫ θ, traceNorm (herm0Coord F θ) ∂(stdGauss (d ^ 2 - 1))) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ d : ℕ, d₀ ≤ d → ∀ F : Fin (d ^ 2 - 1) → Op d, IsHerm0ONB F →
      stdGauss (d ^ 2 - 1) {θ | traceNorm (herm0Coord F θ) ≤ c₀ / 2 * (d : ℝ) ^ ((3 : ℝ) / 2)} ≤
        ENNReal.ofReal (Real.exp (-(a₀ * (d : ℝ) ^ 2))) := by sorry

end LimitedEntanglementTomography.LowerBound
