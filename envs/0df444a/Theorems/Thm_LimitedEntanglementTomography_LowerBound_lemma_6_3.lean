-- Prove2me | Theorems.Thm_LimitedEntanglementTomography_LowerBound_lemma_6_3
-- name    : LimitedEntanglementTomography.LowerBound.lemma_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:13:07.150356+00:00
-- url     : https://prove2.me/theorems/3de57ee7-7a47-4816-9925-241b6c4ff6a1
-- title:
--   Lemma 6.3 — Gaussian Hermitian norm estimates (46)–(48)
-- statement:
--   There are absolute constants $C_0,c_0>0$ and $d_0\in\mathbb N$ such that, for every $d\ge d_0$ and the standard Gaussian $Z$ on $\mathrm{Herm}_0(\mathbb C^d)$,
--   $$\Pr\big[\|Z\|_{\mathrm{op}}\le C_0\sqrt d\,\big]\ge\frac9{10},\qquad \Pr\Big[\|Z\|_F^2\ge\frac{d^2-1}2\Big]\ge\frac9{10},\qquad \mathbb E\|Z\|_1\ge c_0\,d^{3/2}.$$
--
--   All three hold with one choice of $(C_0,c_0,d_0)$. They control the truncation event and the trace-norm small balls of the prior.
--
--   Differences from the source:
--   - encoding: one fixed Frobenius-orthonormal basis F_1,…,F_{d²−1} of Herm₀(ℂ^d) → the statement holds for every orthonormal basis F (IsHerm0ONB F); reason: the source fixes an arbitrary such basis, so its claim is the same claim for every basis; trace Fisher information and the standard Gaussian law do not depend on the basis
--   - encoding: random matrices and sets in Herm₀(ℂ^d) → coordinates θ ∈ ℝ^{d²−1} with Δ = ∑_b θ_b F_b (herm0Coord); reason: an isometric linear bijection for the Frobenius norm; laws and events correspond one to one
--   - encoding: probabilities and expectations of nonnegative quantities in ℝ → values of measures in [0,∞] (ENNReal); reason: a probability is the same number; inequalities are unchanged
-- source:
--   Ufuk Keskin, Jason Luo, Mahbod Majid, Matthew Radzihovsky, Tight Lower Bounds for State Tomography with Limited Entanglement, STOC 2027 submission #1625 (October 2026), source.pdf SHA-256 bdd8884c95899a0c563507d1c005e0dee86e418d52478a2e9e6682bb1f9d29c3, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1625.pdf, §6, printed p.24 / PDF p.26, Lemma 6.3 (eqs. (46)–(48))

import Mathlib
import Definitions.Def_LimitedEntanglementTomography_LowerBound_Prior

open scoped ENNReal ComplexOrder

/-!
Ufuk Keskin, Jason Luo, Mahbod Majid, Matthew Radzihovsky, *Tight Lower Bounds for State
Tomography with Limited Entanglement*, STOC 2027 submission #1625 (October 2026), Lemma 6.3, printed p.24 / PDF p.26, eqs. (46)–(48).
-/

namespace LimitedEntanglementTomography.LowerBound

open MeasureTheory ProbabilityTheory Matrix ShadowTomography.ClassicalLB

/-- **Lemma 6.3.** There are absolute constants `C₀, c₀ > 0` and `d₀ ∈ ℕ` such that for every
`d ≥ d₀` and the standard Gaussian `Z` on `Herm₀(ℂ^d)`:
`Pr[‖Z‖_op ≤ C₀ √d] ≥ 9/10` (46), `Pr[‖Z‖_F² ≥ (d² − 1)/2] ≥ 9/10` (47), and
`E ‖Z‖₁ ≥ c₀ d^{3/2}` (48). -/
theorem lemma_6_3 :
    ∃ C₀ c₀ : ℝ, 0 < C₀ ∧ 0 < c₀ ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∀ F : Fin (d ^ 2 - 1) → Op d, IsHerm0ONB F →
        ENNReal.ofReal (9 / 10) ≤
            stdGauss (d ^ 2 - 1) {θ | opNorm (herm0Coord F θ) ≤ C₀ * Real.sqrt d} ∧
        ENNReal.ofReal (9 / 10) ≤
            stdGauss (d ^ 2 - 1) {θ | ((d : ℝ) ^ 2 - 1) / 2 ≤ frobNorm (herm0Coord F θ) ^ 2} ∧
        c₀ * (d : ℝ) ^ ((3 : ℝ) / 2) ≤ ∫ θ, traceNorm (herm0Coord F θ) ∂(stdGauss (d ^ 2 - 1)) := by sorry

end LimitedEntanglementTomography.LowerBound
