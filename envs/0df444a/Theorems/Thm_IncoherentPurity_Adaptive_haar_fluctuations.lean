-- Prove2me | Theorems.Thm_IncoherentPurity_Adaptive_haar_fluctuations
-- name    : IncoherentPurity.Adaptive.haar_fluctuations
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:57:46.2872+00:00
-- url     : https://prove2.me/theorems/b2e55cd4-8429-4ea0-acfe-9a794b6b6d7a
-- title:
--   Lemma 3.5 — Haar fluctuations
-- statement:
--   Let $d\ge1$ and let $\rho$ be any state. For a Haar basis write $\mu_j=\mathbb E Q_j$, $\mu_{22}=\mathbb E Q_2^2$, $\Delta=\rho-I/d$, $x=\operatorname{tr}\Delta^2$, and $t_j=\operatorname{tr}\Delta^j$. Then
--
--   $$\mu_{22}-\mu_2^2=\frac{2[d(d+1)t_4+(d^2+3d+3)x^2]}{d(d+1)^2(d+2)(d+3)},$$
--   $$\mu_3-\mu_{22}=\frac{2d(d+3)t_3-2dt_4-(d^2+6d+6)x^2+(d^2+5d+6)x}{d(d+1)(d+2)(d+3)}.$$
--
--   Both moments are finite. The formulas retain the two distinct Haar fluctuation contributions.
--
--   Differences from the source:
--   - encoding: matrix, probability and asymptotic notation in the paper → finite matrix coordinates, explicit experiment measures, and universal real constants; reason: the representations retain every source instance and clause; finite-moment conclusions prevent default-zero integrals
--   - encoding: well-defined finite moments of the stated experiments → entrywise Integrable or MemLp 2 conclusions alongside the original moment or variance identities; reason: the experiments have bounded observations on the stated count domains; no additional hypothesis or source instance is imposed
--   - generalization: Section 3 context d ≥ 2 (Theorem 3.1, Proposition 3.2); the lemma itself states no restriction → every dimension d ≥ 1; reason: the printed lemma carries no dimension hypothesis; at d = 1 the only state is ρ = 1, every Q_k = 1 and both sides agree, so the Lean statement specializes to every source instance d ≥ 2
-- source:
--   Lee–Wadhwa, Optimal Purity Estimation with Incoherent Measurements, STOC 2027 submission #66 (2026), pinned source.pdf; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/66.pdf; SHA-256 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce, Lemma 3.5, PDF p.11 = printed p.11

import Definitions.Def_IncoherentPurity_Adaptive_Estimators
import Definitions.Def_IncoherentPurity_Adaptive_Analytic

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Frobenius
set_option autoImplicit false
noncomputable section

namespace IncoherentPurity.Adaptive

/-- Lemma 3.5, PDF p.11, pinned source hash 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce. -/
theorem haar_fluctuations {d : ℕ} (hd : 0 < d) (H : HaarBasis d) (ρ : State d) :
  MemLp (fun U => Q ρ.val U 2) 2 H.law ∧ Integrable (fun U => Q ρ.val U 3) H.law ∧
  mu22 H ρ.val - (mu H ρ.val 2)^2 =
    2 * ((d : ℝ)*((d : ℝ)+1)*powerSum (centered ρ.val) 4 +
      ((d : ℝ)^2+3*d+3)*(excess ρ.val)^2) /
      ((d : ℝ)*((d : ℝ)+1)^2*((d : ℝ)+2)*((d : ℝ)+3)) ∧
  mu H ρ.val 3 - mu22 H ρ.val =
    (2*(d : ℝ)*((d : ℝ)+3)*powerSum (centered ρ.val) 3 -
      2*(d : ℝ)*powerSum (centered ρ.val) 4 -
      ((d : ℝ)^2+6*d+6)*(excess ρ.val)^2 + ((d : ℝ)^2+5*d+6)*excess ρ.val) /
      ((d : ℝ)*((d : ℝ)+1)*((d : ℝ)+2)*((d : ℝ)+3)) := by sorry

end IncoherentPurity.Adaptive
