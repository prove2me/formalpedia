-- Prove2me | Theorems.Thm_GrothendieckPD_Digits_qCert_discretization_bridge
-- name    : GrothendieckPD.Digits.qCert_discretization_bridge
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:15:27.053509+00:00
-- url     : https://prove2.me/theorems/14f49dd5-8087-4362-8240-0ac43e44742b
-- title:
--   Theorem 4.1: discretization from the certificate game to $K_G$
-- statement:
--   Let $q$ be the explicit Hermite projection game of Eq. (4.1), so in particular $q_1=1$, and let $v_\infty(q)$ be its Boolean game value. For every real $c>0$ satisfying
--
--   $$
--   v_\infty(q)\le c,
--   $$
--
--   the Grothendieck constant obeys
--
--   $$
--   \frac1c\le K_G.
--   $$
--
--   This is the discretization bridge used in Theorem 4.1. It transfers an upper bound for the explicit Gaussian projection game into a lower bound for $K_G$; the positivity hypothesis makes the reciprocal inequality meaningful.
--
--   **Formalization Note** The certificate sequence is `qCert`, and $c^{-1}$ is the multiplicative inverse in $\mathbb R$.
-- source:
--   Steven Heilman, Chris Jones, Giulio Malavolta, Primal/Dual Method for the Grothendieck Constant, STOC 2027 submission #820 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/820.pdf, Theorem 4.1 and its proof, p. 11 (standard discretization argument, citing Pis12, Theorems 2.4 and 2.5); Hermite projection games and the ratio SDP(Q)/OPT(Q), §2.1, p. 3

import Mathlib
import Definitions.Def_GrothendieckPD_Digits_FiniteGames

/-- Standard discretization bridge in the proof of Theorem 4.1 for the
certificate sequence `qCert` of Eq. (4.1). -/
theorem GrothendieckPD.Digits.qCert_discretization_bridge (c : ℝ) (hc : 0 < c)
    (hqc : gameValueInf qCert ≤ c) :
    c⁻¹ ≤ GrothendieckConstant.grothendieckConst := by sorry
