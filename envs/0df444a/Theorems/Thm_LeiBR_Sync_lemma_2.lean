-- Prove2me | Theorems.Thm_LeiBR_Sync_lemma_2
-- name    : LeiBR.Sync.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:08:41.860785+00:00
-- url     : https://prove2.me/theorems/381bd507-1c38-440c-a707-e7737fcd196b
-- title:
--   Lemma 2 — $z c^z\le D q^z$ for $0<c<q<1$ and $D\ge 1/\ln((q/c)^e)$
-- statement:
--   Let $0<c<1$, $c<q<1$ and
--   $$D\ge\frac1{\ln\big((q/c)^e\big)}=\frac{1}{e\,\ln(q/c)} .$$
--   Then for every real $z\ge0$,
--   $$z\,c^z\le D\,q^z .$$
--
--   The lemma converts the factor $k c^k$ that appears when a geometric recursion is driven by a geometric perturbation into a pure geometric rate $q^k$ with an explicit constant.
--
--   **Formalization Note** $z$ is real and the powers are real powers. The paper's $\ln(q/c)^e$ is $\ln((q/c)^e)=e\ln(q/c)$, as its proof's last display shows.
-- source:
--   Lei, Shanbhag, Pang & Sen, On Synchronous, Asynchronous, and Randomized Best-Response Schemes for Stochastic Nash Games, arXiv:1704.04578v2, p. 9, Lemma 2

import Mathlib

namespace LeiBR.Sync

/-- Lemma 2, p. 9: for `0 < c < q < 1` and `D ≥ 1/ln((q/c)^e) = 1/(e · ln(q/c))`,
`z c^z ≤ D q^z` for every real `z ≥ 0`. -/
theorem lemma_2 (c q D : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hcq : c < q) (hq1 : q < 1)
    (hD : 1 / (Real.exp 1 * Real.log (q / c)) ≤ D) :
    ∀ z : ℝ, 0 ≤ z → z * c ^ z ≤ D * q ^ z := by sorry

end LeiBR.Sync
