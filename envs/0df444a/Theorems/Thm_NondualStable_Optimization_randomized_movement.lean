-- Prove2me | Theorems.Thm_NondualStable_Optimization_randomized_movement
-- name    : NondualStable.Optimization.randomized_movement
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:45:38.61544+00:00
-- url     : https://prove2.me/theorems/61ceb7e7-939b-4ba2-9fab-fad3feb2061a
-- title:
--   Proposition 11 — Movement of the feasible randomized selector
-- statement:
--   Fix admissible $p,q$, dimension $d\ge1$, radius $R>0$, integer horizon $H\ge1$ and $0<\delta<1$. Put $r=\min\{q,2\}$, $r^*=r/(r-1)$ and $E_{\rm samp}=E_{\rm sol}=E=(R/4)H^{-\rho}$. For
--   $$N\ge \max\{4^{r^*},8\}\left[(R/E)^{r^*}+(R/E)^2\log((H+1)/\delta)\right],$$
--   use fresh independent Gaussian samples after each adaptive body is known and feasible numerical samples within $E$ of their exact counterparts. All numerical averages belong to their requested bodies on every tape. With probability at least $1-\delta$, simultaneously at every requested body,
--   $$\|\widehat C_N(K^t)-C(K^t)\|_r\le 2R N^{-1/r^*}+R\sqrt{2\log((H+1)/\delta)/N},\qquad \|\hat z^t-C(K^t)\|_q\le2E,$$
--   and the numerical path has movement at most $B(H)+R H^{1-\rho}$, where $B(H)$ is the quantitative reference-center profile with a constant depending only on $q$.
--
--   This retains the source's full movement conclusion, its sampling exponent and its unconditional feasibility. The explicit empirical bound is (35), and the added path error is exactly (37).
--
--   Differences from the source:
--   - encoding: real coordinate vectors and exponents in [1,∞] → Fin d → ℝ and extended nonnegative exponents, using the published PiLp norm and reciprocal infinity equal to zero; reason: the same finite-dimensional norms, closed balls and endpoint cases
--   - encoding: randomized procedures and adaptive oracle choices → independent standard Gaussian product tapes and jointly measurable causal oracle or request maps; reason: probabilities refer to measurable random procedures; arbitrary measurable history-dependent bounded subgradient choices remain allowed
--   - encoding: the unspecified sufficiently large Cr in (17) → Cr=max{4^(r*),8}; reason: (35) makes each empirical-error term at most Esamp/2 with this choice
--   - encoding: Õ movement in (18) → the explicit reference movement profile plus R H^(1-rho), simultaneous (35), and the center error bound; reason: these are exactly the inequalities in the proof, including both numerical and sampling errors
-- source:
--   David Martínez-Rubio, Cristóbal Guzmán, STOC 2027 submission #415 (October 2026), printed p. 11/PDF p. 12, Proposition 11 and (17)–(19); proof printed pp. 23–25/PDF pp. 24–26, (35)–(37)

import Definitions.Def_NondualStable_Optimization_Sampling
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace NondualStable.Optimization

/-- Proposition 11, printed p.11 / PDF p.12; (17), (35)-(37).
Fresh Gaussian blocks follow each adaptive request. All numerical samples
are feasible on every tape; only concentration and movement are probabilistic. -/
theorem randomized_movement (q : ℝ≥0∞) (hq : 1 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℝ≥0∞, admissible p q →
      ∀ d H N : ℕ, 0 < d → 1 ≤ H → 0 < N →
      ∀ R δ : ℝ, 0 < R → 0 < δ → δ < 1 →
      let E := R / 4 * (H : ℝ) ^ (-rate p q)
      sampleCount q R E H δ ≤ (N : ℝ) →
      ∀ A : SampledRequests d, SamplingConditions p q R E H N A →
        (∀ ω, ∀ t ≤ H, numericalAverage N A t ω ∈ A.request t ω) ∧
        MeasurableSet {ω | ∀ t ≤ H,
          lpNorm (tailExponent q) (empirical p q R H N A t ω - center p q R H (A.request t ω)) ≤
            2 * R * (N : ℝ) ^ (-recip (dual (tailExponent q))) +
              R * Real.sqrt (2 * Real.log ((H + 1 : ℕ) / δ) / N)} ∧
        tapeLaw {ω | (∀ t ≤ H,
          lpNorm (tailExponent q) (empirical p q R H N A t ω - center p q R H (A.request t ω)) ≤
            2 * R * (N : ℝ) ^ (-recip (dual (tailExponent q))) +
              R * Real.sqrt (2 * Real.log ((H + 1 : ℕ) / δ) / N)) ∧
          (∀ t ≤ H, lpNorm q (numericalAverage N A t ω - center p q R H (A.request t ω)) ≤ 2 * E) ∧
          movement q H (fun t => numericalAverage N A t ω) ≤
            movementProfile C p q d R H + R * (H : ℝ) ^ (1 - rate p q)} ≥ ENNReal.ofReal (1 - δ) := by sorry

end NondualStable.Optimization
