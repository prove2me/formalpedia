-- Prove2me | Theorems.Thm_IncoherentPurity_Adaptive_haar_moments
-- name    : IncoherentPurity.Adaptive.haar_moments
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:57:53.531879+00:00
-- url     : https://prove2.me/theorems/cb00e26c-6585-4d48-8a65-c2c4f493d88b
-- title:
--   Lemma 2.5 — Haar tensor moments
-- statement:
--   Let $d\ge1$, let $v$ be a Haar-random unit vector in $\mathbb C^d$, and let $r$ be any natural number. Writing $W_\pi$ for permutation of the tensor factors,
--
--   $$\mathbb E(|v\rangle\langle v|)^{\otimes r}=\frac{\sum_{\pi\in S_r}W_\pi}{\prod_{j=0}^{r-1}(d+j)}.$$
--
--   The tensor moment is integrable. At $r=0$ the product and tensor power are identities. This is the common moment identity needed by both estimators.
--
--   Differences from the source:
--   - encoding: matrix, probability and asymptotic notation in the paper → finite matrix coordinates, explicit experiment measures, and universal real constants; reason: the representations retain every source instance and clause; finite-moment conclusions prevent default-zero integrals
--   - encoding: well-defined finite moments of the stated experiments → entrywise Integrable or MemLp 2 conclusions alongside the original moment or variance identities; reason: the experiments have bounded observations on the stated count domains; no additional hypothesis or source instance is imposed
-- source:
--   Lee–Wadhwa, Optimal Purity Estimation with Incoherent Measurements, STOC 2027 submission #66 (2026), pinned source.pdf; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/66.pdf; SHA-256 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce, Lemma 2.5, PDF p.9 = printed p.9

import Definitions.Def_IncoherentPurity_Adaptive_Estimators
import Definitions.Def_IncoherentPurity_Adaptive_Analytic

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Frobenius
set_option autoImplicit false
noncomputable section

namespace IncoherentPurity.Adaptive

/-- Lemma 2.5, PDF p.9, pinned source hash 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce. -/
theorem haar_moments {d : ℕ} (hd : 0 < d) (H : HaarBasis d) (r : ℕ) :
  (∀ i j, Integrable (fun v => tensorPower (outer v) r i j) (pureHaar H)) ∧
  (Matrix.of fun i j => ∫ v, tensorPower (outer v) r i j ∂pureHaar H) =
    (1 / (∏ j : Fin r, ((d : ℝ) + j))) • ∑ π : Equiv.Perm (Fin r), permutationOp d r π := by sorry

end IncoherentPurity.Adaptive
