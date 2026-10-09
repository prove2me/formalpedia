-- Prove2me | Theorems.Thm_OnlineCRS_Submod_char_crs_is_crs
-- name    : OnlineCRS.Submod.char_crs_is_crs
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:22:03.750641+00:00
-- url     : https://prove2.me/theorems/095c470d-6ecb-4f20-9a3d-bc1abaf73b3b
-- title:
--   §3, p. 16 — the characteristic CRS π̄ is a true CRS for P
-- statement:
--   Let $\mathcal F$ be a down-closed feasible family and $P\subseteq[0,1]^N$ a relaxation of it ($\mathbf 1_I\in P\iff I\in\mathcal F$). Let $\pi$ be a randomized greedy OCRS for $\mathcal F$, with families $\mathcal F_x$. Then its characteristic CRS $\bar\pi$ is a CRS for $P$: for every input $x$ it is a probability distribution over maps, and every map in its support satisfies, for every $A\subseteq N$,
--   $$\bar\pi(A)\subseteq A\qquad\text{and}\qquad \mathbf 1_{\bar\pi(A)}\in P .$$
--
--   This is the remark following Definition 3.2 and Observation 3.3: it is what allows Lemma 3.5, a statement about CRSs for $P$, to be applied to $\bar\pi$.
-- source:
--   arXiv:1508.00142v2, §3, p. 16, the sentence between Definition 3.2 and Observation 3.3

import Mathlib
import Definitions.Def_OnlineCRS_Matroid_Basics
import Definitions.Def_OnlineCRS_Submod_Model
import Definitions.Def_OnlineCRS_Submod_CRS

namespace OnlineCRS.Submod

/-- §3, p. 16, the sentence after Definition 3.2: `π̄(A)` obeys the polytope `P` and `π̄(A) ⊆ A`, so the
characteristic CRS `π̄` of a randomized greedy OCRS for the feasible sets `𝓕`, where `P` is a relaxation
of `𝓕`, is a true CRS for `P`. -/
theorem char_crs_is_crs {α : Type} [Fintype α] [DecidableEq α] (𝓕 : Finset α → Prop)
    (P : Set (α → ℝ)) (hPoly : IsPolytope P) (hRel : IsRelaxation 𝓕 P)
    (w : (α → ℝ) → Finset (Finset α) → ℝ) (hw : OnlineCRS.Matroid.IsRandGreedyOCRS 𝓕 w) :
    IsCRS P (charCRS w) := by sorry

end OnlineCRS.Submod
