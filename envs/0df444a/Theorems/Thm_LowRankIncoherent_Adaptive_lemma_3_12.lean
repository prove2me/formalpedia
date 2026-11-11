-- Prove2me | Theorems.Thm_LowRankIncoherent_Adaptive_lemma_3_12
-- name    : LowRankIncoherent.Adaptive.lemma_3_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T13:19:14.82296+00:00
-- url     : https://prove2.me/theorems/9602fa5c-25df-4b5b-8961-3b22bd863b24
-- title:
--   Lemma 3.12 — positive semidefinite rank truncation
-- statement:
--   Let $X\succeq0$ have rank at most $r$ in dimension $D≥1$, and let $\widehat X$ be Hermitian with $\|\widehat X-X\|_∞≤θ$. Let $S$ retain the largest positive eigenvalues of $\widehat X$, up to $r$, with the remaining eigenvalues zero. Then
--   $$S\succeq0,\qquad\operatorname{rank}S≤r,\qquad\|S-X\|_∞≤2θ.$$
--   Ties may be split within their eigenspace. This is the complete deterministic approximation guarantee for the first batch's truncation.
--
--   Differences from the source:
--   - encoding: finite complex registers and the source conventions → Fin-indexed matrices, explicit positivity and sample-count domains, and the operational definitions in this mission; reason: coordinate and domain conventions preserve every defined physical instance; no statistical guarantee is assumed
--   - generalization: the standing rank regime 1≤r≤D → any natural rank budget, also r=0 or r>D; reason: for r=0 the positive semidefinite target is zero and the retained matrix is zero; for r>D all positive eigenvalues are retained, with the same approximation argument and constant 2
-- source:
--   Aadil Oufkir, Kean Chen, STOC 2027 submission #364 (October 2026), Lemma 3.12, printed p. 25 = PDF p. 25; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/364.pdf

import Definitions.Def_LowRankIncoherent_Adaptive_Algorithm

open Matrix MeasureTheory
open scoped MatrixOrder ComplexOrder ENNReal
noncomputable section

namespace LowRankIncoherent.Adaptive

theorem lemma_3_12 {d r : ℕ} (hd : 0 < d) (X Xhat S : Input d) (θ : ℝ)
    (hX : X.PosSemidef) (hrank : X.rank ≤ r) (hhat : Xhat.IsHermitian)
    (herr : opNorm (Xhat-X) ≤ θ) (hS : IsTruncation r Xhat S) :
    S.PosSemidef ∧ S.rank ≤ r ∧ opNorm (S-X) ≤ 2*θ := by sorry

end LowRankIncoherent.Adaptive
