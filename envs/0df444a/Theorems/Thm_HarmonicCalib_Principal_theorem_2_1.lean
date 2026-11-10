-- Prove2me | Theorems.Thm_HarmonicCalib_Principal_theorem_2_1
-- name    : HarmonicCalib.Principal.theorem_2_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:06:30.577271+00:00
-- url     : https://prove2.me/theorems/64d24950-f02b-4969-8bf2-849dc292f8ba
-- title:
--   Theorem 2.1 — the general algorithm (5) has $\mathrm{Cal}_{L,T} \le 3\,\Gamma^{(T)}_{\tilde Y, L^\circ}(H)$
-- statement:
--   Let $Y \subseteq \mathbb R^d$ be nonempty, compact and convex, and let $L \subseteq \mathbb R^d$ be a norm unit ball. For every $T$, every $H \in \widehat{\mathcal H}_T$, every $p_{\mathrm{init}} \in Y$ and every outcome sequence $y_0, \dots, y_{T-1} \in Y$, the algorithm (5) parameterized by $H$ satisfies
--   $$\mathrm{Cal}_{L,T} \le 3\, \Gamma^{(T)}_{\tilde Y, L^\circ}(H),$$
--   with $\tilde Y = Y - c_Y$.
--
--   Differences from the source:
--   - generalization: Cal_{L,T} = O(Γ^{(T)}_{Ỹ,L°}(H)) → Cal_{L,T} ≤ 3·Γ^{(T)}_{Ỹ,L°}(H), the constant derived in the proof (p. 10: 3 for T ≥ 2, 2 for T = 1); reason: an explicit absolute constant implies the O(·) statement; Theorem 1.2's proof (p. 11) uses this 3
--   - generalization: T rounds (T ≥ 1 implicit) → every T : ℕ; reason: T = 0 adds only the trivial instance Cal = 0 = Γ
--   - reading: c_Y the center of mass of Y (undefined under Lebesgue measure on ℝ^d when Y is lower-dimensional, e.g. Δ_d) → centerOfMass Y: the barycenter of the k-dimensional Hausdorff measure on Y, k = dimension of the affine span of Y; reason: the uniform measure on Y relative to its affine hull; it is the Lebesgue barycenter for full-dimensional Y, (1/d)·1 for Δ_d and the point itself for a singleton
--   - encoding: ℝ^d with the standard inner product → EuclideanSpace ℝ (Fin d) with ⟪·,·⟫_ℝ; reason: the same space; coordinates are x i for i : Fin d
--   - encoding: the algorithm (5) with P, Q recovered from H = Q − Pᵀ → genStored: p_s = ∑_{t≤s} (−H_ts) y_t; genMu: μ_0 = δ_{p_init}, μ_t = ∑_{s<t} H_ts δ_{p_s}; reason: with P lower and Q strictly lower triangular, H_ts = Q_ts for s < t and H_ts = −P_st for t ≤ s, so P and Q are read off H
--   - encoding: finite distributions μ_t over forecasts, Cal summed over distinct points with positive total weight → μ_t : ℝ^d →₀ ℝ (equal points are one key) and calError sums over the points of the supports with ∑_t μ_t(p) > 0, norm gauge L; reason: the same quantity; aggregation of equal forecast values is automatic
--   - encoding: Γ^{(T)} and γ as real suprema → Gamma and gammaCoef valued in EReal (iSup); reason: an EReal supremum is never a junk value; on nonempty compact sets Γ is finite and the EReal comparison is the real one
-- source:
--   Fishelson and Mohri (2026), High-Dimensional Online Calibration from Harmonic Weights, arXiv:2610.07740 (version dated October 29, 2026; PDF SHA256 62ac31a3…), Theorem 2.1, p. 8 (constant 3 from its proof, p. 10)

import Mathlib
import Definitions.Def_HarmonicCalib_Principal_Geometry
import Definitions.Def_HarmonicCalib_Principal_Hilbert
import Definitions.Def_HarmonicCalib_Principal_Discrepancy
import Definitions.Def_HarmonicCalib_Principal_Calibration

namespace HarmonicCalib.Principal

/-- Theorem 2.1 (p. 8), with the constant `3` its proof gives (p. 10): for every nonempty compact
convex forecast set `Y ⊆ ℝ^d`, every norm unit ball `L`, every `T`, every `H ∈ Ĥ_T`, every
`p_init ∈ Y` and every outcome sequence `y_0, …, y_{T-1} ∈ Y`, the algorithm (5) parameterized by
`H` has `Cal_{L,T} ≤ 3 Γ^{(T)}_{Ỹ, L°}(H)`. -/
theorem theorem_2_1 :
    ∀ (d T : ℕ) (Y L : Set (EuclideanSpace ℝ (Fin d))),
      Y.Nonempty → IsCompact Y → Convex ℝ Y → IsNormBall L →
      ∀ H : Matrix (Fin T) (Fin T) ℝ, IsAdmissible T H →
      ∀ pinit ∈ Y, ∀ y : Fin T → EuclideanSpace ℝ (Fin d), (∀ t, y t ∈ Y) →
        ((calError L T (genMu H pinit y) y : ℝ) : EReal) ≤
          3 * Gamma (centered Y) (polar L) T H := by sorry

end HarmonicCalib.Principal
