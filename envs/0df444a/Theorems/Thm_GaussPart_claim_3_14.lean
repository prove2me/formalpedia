-- Prove2me | Theorems.Thm_GaussPart_claim_3_14
-- name    : GaussPart.claim_3_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:31:57.093242+00:00
-- url     : https://prove2.me/theorems/a714910c-cf78-4671-9dce-44707bb13a2d
-- title:
--   Claim 3.14 — guarantees on certified cells
-- statement:
--   In the proof of Theorem 3.1 ($P=N(0,I_d)$, $Q$ $(q,\sigma)$-smooth), on the success event $\Omega$: every certified cell $R\in\mathcal G$ satisfies
--   $$Q(R)>\xi/4\qquad\text{and}\qquad\operatorname{diam}(R)\le\delta_0\sqrt L,$$
--   and $P\mid R$ and $Q\mid R$ match their first $k$ moments on $V_R^\perp$ with slack $\Delta$.
--
--   With $\delta_0=\delta/\sqrt L$ and $\xi/4\ge1/B$ this gives items (i)–(iii) of Theorem 3.1 for the certified cells.
--
--   **Formalization Note** Algorithm 1 is a valid trace with knobs $K$ (the claim uses $\xi=K.\xi$, $\delta_0=K.\delta_0$, $L=K.L$); $\mathcal G$ is the list of cells of $\mathcal U_{L+1}$ tagged good. The parts of $\Omega$ used are hypotheses: mass estimates within $\xi/4$ (`EstimatesAccurate`) and the None conclusion of Corollary C.1 at every certified cell (`FinderNoneSound`). The diameter is in the all-pairs form.
--
--   Differences from the source:
--   - generalization: Algorithm 1 with the Parameter Choices, on Ω → any valid trace with any knobs K, with ξ, δ₀, L read from K, under the parts of Ω the claim uses (mass estimates within ξ/4; the None conclusion of Corollary C.1); reason: the proof uses only these; the Parameter Choices and Algorithm 1 are an instance
--   - encoding: diam(R) ≤ δ₀√L → ∥proj_{V_R}x − proj_{V_R}y∥ ≤ δ₀√L for all x, y ∈ R; reason: same condition, no supremum default
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Claim 3.14, p.27 (PDF p.29); success event Ω, p.26; Algorithm 1, p.19

import Mathlib
import Definitions.Def_GaussPart_IsSmooth
import Definitions.Def_GaussPart_IsGoodOutput
import Definitions.Def_GaussPart_Trace
import Definitions.Def_GaussPart_TraceEvents

open MeasureTheory ProbabilityTheory

namespace GaussPart

/-- **Claim 3.14** (Guarantees on Certified Cells).

arXiv:2611.05264 (copy with sha256 7e0ca6d4…), Claim 3.14, p.27 (PDF p.29), in the proof of
Theorem 3.1; the success event `Ω` is on p.26 (PDF p.28); Algorithm 1, p.19.

"Every R ∈ G satisfies q_R > ξ/4 and diam(R) ≤ δ₀√L. Moreover, P | R and Q | R match their first k
moments on V_R^⊥ with slack ∆."

**Formalization Note.**
* `P = N(0, I_d)`, `Q` `(q, σ)`-smooth with the ranges of Theorem 3.1. "Algorithm 1" is a valid
  `Trace` with parameters `K` (any parameters, not only the Parameter Choices of p.21; the claim
  uses only `ξ = K.ξ`, `δ₀ = K.δ₀`, `L = K.L`). `G` is the list of cells of `U_{L+1}` tagged good.
* The parts of `Ω` the claim uses are hypotheses: every mass estimate of a non-terminal cell has
  error at most `ξ/4` (`EstimatesAccurate`), and every finder that returned None satisfies item 2
  of Corollary C.1 on `V_R^⊥` (`FinderNoneSound`).
* `diam(R) ≤ δ₀√L` is `DiamLE R (δ₀√L)` (the `∀ x y` form in `V_R`, not `Metric.diam`); moment
  matching is Definition 2.2 for `P | R` and `Q | R` (`ProbabilityTheory.cond`) on `V_R^⊥`. -/
theorem claim_3_14 {d : ℕ} (hd : 1 ≤ d) (k : ℕ) (hk : 1 ≤ k) (Q : Measure (Vec d))
    [IsProbabilityMeasure Q] (q σ Δ : ℝ) (hq : 1 ≤ q) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hΔ : 0 < Δ)
    (hΔ1 : Δ < 1 / 2) (hs : IsSmooth (stdGaussian (Vec d)) Q q σ) (K : Knobs) (tr : Trace d)
    (htr : tr.IsValid K) (hest : tr.EstimatesAccurate Q K (K.ξ / 4))
    (hnone : tr.FinderNoneSound Q K k Δ) :
    ∀ R ∈ tr.tagged (K.L + 1) Tag.good,
      K.ξ / 4 < (Q (cellSet R)).toReal ∧
      DiamLE R (K.δ₀ * Real.sqrt K.L) ∧
      MatchesMoments (ProbabilityTheory.cond (stdGaussian (Vec d)) (cellSet R))
        (ProbabilityTheory.cond Q (cellSet R)) (constraintSpace R)ᗮ k Δ := by sorry

end GaussPart
