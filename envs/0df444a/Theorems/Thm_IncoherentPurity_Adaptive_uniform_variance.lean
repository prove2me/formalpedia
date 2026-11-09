-- Prove2me | Theorems.Thm_IncoherentPurity_Adaptive_uniform_variance
-- name    : IncoherentPurity.Adaptive.uniform_variance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:57:53.511359+00:00
-- url     : https://prove2.me/theorems/2dc7e2cb-a2d8-4640-a10d-21fa7d207896
-- title:
--   Proposition 3.2 — Uniform batch variance bound
-- statement:
--   For every $d\ge2$, $B\ge1$, $s\ge2$, and state $\rho$, the batch estimator is square integrable and, with $x=\operatorname{tr}(\rho-I/d)^2$, satisfies
--
--   $$\operatorname{Var}(\widehat P_2)\le\frac1B\left(\frac{12d}{s^2}+\frac{12x}{s}+\frac{4x^2}{d}\right).$$
--
--   The constants are uniform over all states and batch parameters.
--
--   Differences from the source:
--   - encoding: matrix, probability and asymptotic notation in the paper → finite matrix coordinates, explicit experiment measures, and universal real constants; reason: the representations retain every source instance and clause; finite-moment conclusions prevent default-zero integrals
--   - encoding: well-defined finite moments of the stated experiments → entrywise Integrable or MemLp 2 conclusions alongside the original moment or variance identities; reason: the experiments have bounded observations on the stated count domains; no additional hypothesis or source instance is imposed
-- source:
--   Lee–Wadhwa, Optimal Purity Estimation with Incoherent Measurements, STOC 2027 submission #66 (2026), pinned source.pdf; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/66.pdf; SHA-256 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce, Proposition 3.2, PDF p.9 = printed p.9

import Definitions.Def_IncoherentPurity_Adaptive_Estimators
import Definitions.Def_IncoherentPurity_Adaptive_Analytic

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Frobenius
set_option autoImplicit false
noncomputable section

namespace IncoherentPurity.Adaptive

/-- Proposition 3.2, PDF p.9, pinned source hash 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce. -/
theorem uniform_variance {d B s : ℕ} (hd : 2 ≤ d) (hB : 1 ≤ B) (hs : 2 ≤ s) (H : HaarBasis d) (ρ : State d) :
  MemLp (batchEstimate (d:=d) (B:=B) (s:=s)) 2 (batchesLaw H ρ.val B s) ∧
  variance (batchEstimate (d:=d) (B:=B) (s:=s)) (batchesLaw H ρ.val B s) ≤
    (1 / (B : ℝ)) * (12*(d : ℝ)/(s : ℝ)^2 + 12*excess ρ.val/(s : ℝ) +
      4*(excess ρ.val)^2/(d : ℝ)) := by sorry

end IncoherentPurity.Adaptive
