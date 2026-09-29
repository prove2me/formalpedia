-- Prove2me | Theorems.Thm_GrothendieckConstant_opt_le_sdp
-- name    : GrothendieckConstant.opt_le_sdp
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T18:22:33.002341+00:00
-- url     : https://prove2.me/theorems/576c16f7-2f63-454c-8fd7-f7bdd149b7b4
-- title:
--   $\mathrm{OPT}(A)\le\mathrm{SDP}(A)$
-- statement:
--   The semidefinite relaxation can only overshoot the discrete optimum: for every $m,n\in\mathbb N$ and every real matrix $A\in\mathbb R^{m\times n}$,
--
--   $$\mathrm{OPT}(A)\le\mathrm{SDP}(A).$$
--
--   The reason is that a sign is a unit vector in dimension one, so every $\pm1$ labeling of the rows and columns is itself a feasible point of the relaxation. This inequality is the trivial half of Grothendieck's inequality and fixes the direction in which the Grothendieck constant measures the gap.
-- source:
--   Li, Saha, Xue, Chaudhuri, Klivans, Kothari, Meka, "Long-Horizon AI Research for Grothendieck Constant: A Case Study in Human-AI Mathematical Collaboration", arXiv:2608.11195v3 (2026), https://arxiv.org/abs/2608.11195, Section 2, p. 3 ("Since every sign is a one-dimensional unit vector, OPT(A) <= SDP(A): the relaxation can only overshoot.")

import Mathlib
import Definitions.Def_GrothendieckConstantDefs

namespace GrothendieckConstant

theorem opt_le_sdp (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) :
    optValue A ≤ sdpValue A := by sorry

end GrothendieckConstant
