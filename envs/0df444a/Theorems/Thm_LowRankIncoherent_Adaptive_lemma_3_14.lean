-- Prove2me | Theorems.Thm_LowRankIncoherent_Adaptive_lemma_3_14
-- name    : LowRankIncoherent.Adaptive.lemma_3_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T13:18:58.189876+00:00
-- url     : https://prove2.me/theorems/794cbacd-5152-4d49-a0aa-662b9309d7aa
-- title:
--   Lemma 3.14 — regularized quadratic-form stability
-- statement:
--   Let $s>0$ and $X,S\succeq0$ in dimension $D≥1$, with $\|S-X\|_∞≤η≤s/4$. Put $F=f_s(X)$, $Z=X_s$, $P_S$ the support projection, and $R=(S+sI)^{-1}P_S$. Then
--   $$0\preceq R\preceq s^{-1}I,\quad\operatorname{rank}R≤\operatorname{rank}S,\quad-3ηF\preceq XRX-Z\preceq3ηF.$$
--   For the Moore–Penrose inverse $F^+$ define $W=RX(F^+)^{1/2}$. It satisfies
--   $$WF^{1/2}=RX,\qquad\operatorname{rank}W≤\operatorname{rank}S,\qquad\|W\|_∞≤2.$$
--   The support inverse includes zero eigenvalues correctly, including $S=0$. These are the full stability and factorization conclusions.
--
--   Differences from the source:
--   - encoding: finite complex registers and the source conventions → Fin-indexed matrices, explicit positivity and sample-count domains, and the operational definitions in this mission; reason: coordinate and domain conventions preserve every defined physical instance; no statistical guarantee is assumed
-- source:
--   Aadil Oufkir, Kean Chen, STOC 2027 submission #364 (October 2026), Lemma 3.14, printed p. 29 = PDF p. 29; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/364.pdf

import Definitions.Def_LowRankIncoherent_Adaptive_Algorithm

open Matrix MeasureTheory
open scoped MatrixOrder ComplexOrder ENNReal
noncomputable section

namespace LowRankIncoherent.Adaptive

theorem lemma_3_14 {d : ℕ} (hd : 0 < d) (X S : Input d) (s η : ℝ)
    (hs : 0 < s) (hX : X.PosSemidef) (hS : S.PosSemidef)
    (herr : opNorm (S-X) ≤ η) (hη : η ≤ s/4) :
    let F := fs s X
    let R := resolvent s S
    let W := R * X * sqrtM (pinv F)
    R.PosSemidef ∧ LE R ((s⁻¹ : ℂ) • 1) ∧ R.rank ≤ S.rank ∧
    LE ((-3*η : ℝ) • F) (X*R*X - regularized s X) ∧
    LE (X*R*X - regularized s X) ((3*η : ℝ) • F) ∧
    W * sqrtM F = R*X ∧ W.rank ≤ S.rank ∧ opNorm W ≤ 2 := by sorry

end LowRankIncoherent.Adaptive
