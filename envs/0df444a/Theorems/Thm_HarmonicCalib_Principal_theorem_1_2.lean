-- Prove2me | Theorems.Thm_HarmonicCalib_Principal_theorem_1_2
-- name    : HarmonicCalib.Principal.theorem_1_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:06:25.480992+00:00
-- url     : https://prove2.me/theorems/68bae1df-aa57-4928-9330-c6d188739df0
-- title:
--   Theorem 1.2 — general geometric guarantee: $\varepsilon$-calibration for $T \ge \exp(C\gamma(Y,L)/\varepsilon)$
-- statement:
--   There is an absolute constant $C > 0$ such that the following holds. Let $L \subseteq \mathbb R^d$ be any norm unit ball and $Y \subseteq \mathbb R^d$ a nonempty compact convex forecast set. For every $\varepsilon > 0$ and every horizon $T$ with
--   $$T \ge \exp\Bigl(\frac{C\,\gamma(Y, L)}{\varepsilon}\Bigr),$$
--   Algorithm 1 achieves $\varepsilon$-calibration in $T$ rounds: for every initial forecast $p_{\mathrm{init}} \in Y$ and every outcome sequence $y_0, \dots, y_{T-1} \in Y$, $\mathrm{Cal}_{L,T}/T \le \varepsilon$. The constant $C$ does not depend on $d$, $Y$, $L$, $\varepsilon$ or $T$; the threshold is $+\infty$ (no $T$ qualifies) when $\gamma(Y,L) = +\infty$.
--
--   Differences from the source:
--   - reading: c_Y the center of mass of Y (undefined under Lebesgue measure on ℝ^d when Y is lower-dimensional, e.g. Δ_d) → centerOfMass Y: the barycenter of the k-dimensional Hausdorff measure on Y, k = dimension of the affine span of Y; reason: the uniform measure on Y relative to its affine hull; it is the Lebesgue barycenter for full-dimensional Y, (1/d)·1 for Δ_d and the point itself for a singleton
--   - encoding: ℝ^d with the standard inner product → EuclideanSpace ℝ (Fin d) with ⟪·,·⟫_ℝ; reason: the same space; coordinates are x i for i : Fin d
--   - encoding: T ≥ exp(Cγ(Y,L)/ε) with γ real → EReal.exp ((C : EReal) * gammaCoef Y L / ε) ≤ (T : ℝ≥0∞); reason: γ is an EReal supremum; for finite γ this is exp(Cγ/ε) ≤ T, and for γ = +∞ the threshold is ∞, so no T qualifies, as with the source's exp(+∞)
--   - encoding: every realized transcript (μ_0, y_0), …, (μ_{T-1}, y_{T-1}) against an adaptive adversary → every outcome sequence y : ℕ → ℝ^d with y t ∈ Y for t < T, μ_t = alg1Mu p_init y t; reason: Algorithm 1 is deterministic and μ_t depends only on y_0, …, y_{t-1}, so transcripts and outcome sequences coincide; values of y after round T-1 are never read
--   - encoding: finite distributions μ_t over forecasts, Cal summed over distinct points with positive total weight → μ_t : ℝ^d →₀ ℝ (equal points are one key) and calError sums over the points of the supports with ∑_t μ_t(p) > 0, norm gauge L; reason: the same quantity; aggregation of equal forecast values is automatic
--   - encoding: Γ^{(T)} and γ as real suprema → Gamma and gammaCoef valued in EReal (iSup); reason: an EReal supremum is never a junk value; on nonempty compact sets Γ is finite and the EReal comparison is the real one
-- source:
--   Fishelson and Mohri (2026), High-Dimensional Online Calibration from Harmonic Weights, arXiv:2610.07740 (version dated October 29, 2026; PDF SHA256 62ac31a3…), Theorem 1.2, p. 5 (restated p. 11)

import Mathlib
import Definitions.Def_HarmonicCalib_Principal_Geometry
import Definitions.Def_HarmonicCalib_Principal_Discrepancy
import Definitions.Def_HarmonicCalib_Principal_Calibration

namespace HarmonicCalib.Principal

/-- Theorem 1.2 (general geometric guarantee, p. 5; restated p. 11): there is an absolute constant
`C > 0` such that for every `d`, every norm unit ball `L ⊆ ℝ^d`, every nonempty compact convex
forecast set `Y ⊆ ℝ^d` and every `ε > 0`, Algorithm 1 achieves `ε`-calibration
(`Cal_{L,T}/T ≤ ε` for every `p_init ∈ Y` and every outcome sequence in `Y`) for every
`T ≥ exp(C γ(Y, L)/ε)`. The threshold is computed in `EReal`/`ℝ≥0∞` (`EReal.exp`), so it is
`∞` (and the statement is empty) exactly when `γ(Y, L) = +∞`. -/
theorem theorem_1_2 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ) (Y L : Set (EuclideanSpace ℝ (Fin d))),
        Y.Nonempty → IsCompact Y → Convex ℝ Y → IsNormBall L →
        ∀ ε : ℝ, 0 < ε → ∀ T : ℕ,
          EReal.exp ((C : EReal) * gammaCoef Y L / (ε : EReal)) ≤ (T : ENNReal) →
          ∀ pinit ∈ Y, ∀ y : ℕ → EuclideanSpace ℝ (Fin d), (∀ t, t < T → y t ∈ Y) →
            alg1Cal L T pinit y / T ≤ ε := by sorry

end HarmonicCalib.Principal
