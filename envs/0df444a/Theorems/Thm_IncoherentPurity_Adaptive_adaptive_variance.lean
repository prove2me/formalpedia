-- Prove2me | Theorems.Thm_IncoherentPurity_Adaptive_adaptive_variance
-- name    : IncoherentPurity.Adaptive.adaptive_variance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:58:02.029592+00:00
-- url     : https://prove2.me/theorems/76aafd4a-30d2-4b10-afe6-2ff248099dfd
-- title:
--   Lemma 4.2 — Adaptive unbiasedness and variance
-- statement:
--   For every $d\ge1$ state and integers $n,m\ge1$, run Algorithm 1 with the uniform POVM snapshots and signed spectral observations. Its law is a probability measure, and its output $Z$ is square integrable with
--
--   $$\mathbb EZ=\operatorname{tr}\rho^2,\qquad\operatorname{Var}Z\le\frac{24d^2}{n^2}+\frac{4\operatorname{tr}\rho^3}{m}+\frac{8d}{mn}.$$
--
--   The correction uses $D_{\rm est}=d^2+d-1$; no positivity requirement is imposed on the preliminary Hermitian estimate.
--
--   Differences from the source:
--   - encoding: matrix, probability and asymptotic notation in the paper → finite matrix coordinates, explicit experiment measures, and universal real constants; reason: the representations retain every source instance and clause; finite-moment conclusions prevent default-zero integrals
--   - encoding: well-defined finite moments of the stated experiments → entrywise Integrable or MemLp 2 conclusions alongside the original moment or variance identities; reason: the experiments have bounded observations on the stated count domains; no additional hypothesis or source instance is imposed
-- source:
--   Lee–Wadhwa, Optimal Purity Estimation with Incoherent Measurements, STOC 2027 submission #66 (2026), pinned source.pdf; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/66.pdf; SHA-256 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce, Lemma 4.2, PDF p.12 = printed p.12

import Definitions.Def_IncoherentPurity_Adaptive_Estimators
import Definitions.Def_IncoherentPurity_Adaptive_Analytic

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Frobenius
set_option autoImplicit false
noncomputable section

namespace IncoherentPurity.Adaptive

/-- Lemma 4.2, PDF p.12, pinned source hash 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce. -/
theorem adaptive_variance {d n m : ℕ} (hd : 0 < d) (hn : 1 ≤ n) (hm : 1 ≤ m) (H : HaarBasis d) (ρ : State d) :
  IsProbabilityMeasure (adaptiveLaw H ρ.val n m) ∧
  MemLp (adaptiveEstimate (d:=d) (n:=n) (m:=m)) 2 (adaptiveLaw H ρ.val n m) ∧
  (∫ a, adaptiveEstimate a ∂adaptiveLaw H ρ.val n m) = powerSum ρ.val 2 ∧
  variance (adaptiveEstimate (d:=d) (n:=n) (m:=m)) (adaptiveLaw H ρ.val n m) ≤
    24*(d : ℝ)^2/(n : ℝ)^2 + 4*powerSum ρ.val 3/(m : ℝ) + 8*(d : ℝ)/((m : ℝ)*n) := by sorry

end IncoherentPurity.Adaptive
