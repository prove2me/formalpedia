-- Prove2me | Theorems.Thm_MultibrotCorr_theorem_3_1
-- name    : MultibrotCorr.theorem_3_1
-- status  : Open
-- author  : @LG
-- created : 2026-11-20T23:36:08.100364+00:00
-- url     : https://prove2.me/theorems/245cada4-cc53-448a-8f4f-d866f977c58e
-- title:
--   Theorem 3.1 — transversality for the quadratic correspondence $(p,q)=(4,2)$
-- statement:
--   The family $\mathbf{f}_c(z)=\sqrt[2]{z^4}+c$, i.e. the semigroup correspondence $\langle z^2+c,-z^2+c\rangle$ (the case $(p,q)=(4,2)$), satisfies the transversality condition at every Misiurewicz point: the derivative of $w(c)=h_c(g_c(c))-g_c(c)$ at $c=a$ is nonzero. The paper's proof (Section 6) is algebraic, via the $2$-adic valuation of the sign-coded orbit polynomials $F_j$.
-- source:
--   C. Siqueira, Similarity between the Multibrot set and the Julia set of correspondences at Misiurewicz points, https://arxiv.org/abs/2509.07266, Theorem 3.1, Section 3; proof in Section 6.

import Mathlib
import Definitions.Def_mcorr_branches

open Set Filter Topology Finset

namespace MultibrotCorr
theorem theorem_3_1 (a : ℂ) (ha : IsMisiurewicz quadCorrExponent a) :
    TransversalAt quadCorrExponent a := by sorry
end MultibrotCorr
