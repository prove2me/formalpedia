-- Prove2me | Theorems.Thm_IncoherentPurity_Adaptive_haar_averages
-- name    : IncoherentPurity.Adaptive.haar_averages
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:58:10.654167+00:00
-- url     : https://prove2.me/theorems/f326c0c6-7c24-4311-b6b2-7e28b02bc3be
-- title:
--   Lemma 3.4 — Haar averages and unbiasedness
-- statement:
--   For any $d\ge1$ state $\rho$, $B\ge1$ independent Haar bases, and $s\ge2$ outcomes per basis, let $P_j=\operatorname{tr}\rho^j$, $\mu_j=\mathbb E_UQ_j$, and let $\widehat P_2$ be the batch estimator. Then
--
--   $$\mu_2=\frac{1+P_2}{d+1},\quad\mu_3=\frac{1+3P_2+2P_3}{(d+1)(d+2)},\quad\mathbb E\widehat P_2=P_2.$$
--
--   The estimator is square integrable. These identities center its variance analysis.
--
--   Differences from the source:
--   - encoding: matrix, probability and asymptotic notation in the paper → finite matrix coordinates, explicit experiment measures, and universal real constants; reason: the representations retain every source instance and clause; finite-moment conclusions prevent default-zero integrals
--   - encoding: well-defined finite moments of the stated experiments → entrywise Integrable or MemLp 2 conclusions alongside the original moment or variance identities; reason: the experiments have bounded observations on the stated count domains; no additional hypothesis or source instance is imposed
--   - generalization: Section 3 context d ≥ 2 (Theorem 3.1, Proposition 3.2); the lemma itself states no restriction → every dimension d ≥ 1; reason: the printed lemma carries no dimension hypothesis; at d = 1 the only state is ρ = 1, every Q_k = 1 and both sides agree, so the Lean statement specializes to every source instance d ≥ 2
-- source:
--   Lee–Wadhwa, Optimal Purity Estimation with Incoherent Measurements, STOC 2027 submission #66 (2026), pinned source.pdf; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/66.pdf; SHA-256 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce, Lemma 3.4, PDF p.10 = printed p.10

import Definitions.Def_IncoherentPurity_Adaptive_Estimators
import Definitions.Def_IncoherentPurity_Adaptive_Analytic

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Frobenius
set_option autoImplicit false
noncomputable section

namespace IncoherentPurity.Adaptive

/-- Lemma 3.4, PDF p.10, pinned source hash 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce. -/
theorem haar_averages {d B s : ℕ} (hd : 0 < d) (hB : 1 ≤ B) (hs : 2 ≤ s) (H : HaarBasis d) (ρ : State d) :
  mu H ρ.val 2 = (1 + powerSum ρ.val 2) / ((d : ℝ)+1) ∧
  mu H ρ.val 3 = (1 + 3 * powerSum ρ.val 2 + 2 * powerSum ρ.val 3) /
    (((d : ℝ)+1) * ((d : ℝ)+2)) ∧
  MemLp (batchEstimate (d:=d) (B:=B) (s:=s)) 2 (batchesLaw H ρ.val B s) ∧
  (∫ a, batchEstimate a ∂batchesLaw H ρ.val B s) = powerSum ρ.val 2 := by sorry

end IncoherentPurity.Adaptive
