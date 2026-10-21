-- Prove2me | Theorems.Thm_NonExclEncroach_Channels_lemma_4_thresholds
-- name    : NonExclEncroach.Channels.lemma_4_thresholds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:35.411984+00:00
-- url     : https://prove2.me/theorems/4af92109-a583-4fa1-87ca-868235fbc9d5
-- title:
--   Lemma 4, p. 18 — the cost thresholds are ordered: c0 ≤ c1 ≤ c2 ≤ c3 for θ12 ∈ (0, 1)
-- statement:
--   For every $\theta\in(0,1)$ the thresholds of Table 2,
--   $$c_0=-\frac{(2-\theta)(8-\theta^2-\theta^3)}{2(8-5\theta^2)},\qquad c_1=\frac{4\theta-14\theta^2+5\theta^3-\theta^4}{32-26\theta^2},$$
--   $$c_2=\frac{32\theta-80\theta^2-32\theta^3-14\theta^4-8\theta^5+4\theta^6-\theta^7}{2(1+\theta)(128-16\theta^2-13\theta^4)},\qquad c_3=\frac{384-64\theta+8\theta^2-24\theta^3-60\theta^4+6\theta^5-9\theta^6+\theta^7+\theta^8}{2(320-36\theta^2-42\theta^4+\theta^6)},$$
--   satisfy
--   $$c_0\le c_1\le c_2\le c_3 .$$
--
--   These are the boundaries between the Direct Only, Direct Only Boundary and Reseller & Direct regimes of Lemma 4; their ordering is what makes the three regimes partition the cost range $[c_0,c_3]$.
--
--   **Formalization Note** The appendix states $c_1\le c_2\le c_3$ for $\theta\in[0,1]$; the statement is made on the standing range $\theta\in(0,1)$, and includes $c_0\le c_1$ from the statement of Lemma 4.
-- source:
--   Hotkar & Gilbert, Supplier Encroachment in a Non-Exclusive Reselling Channel, SSRN working paper 3238502, p. 18 (PDF 18), Lemma 4; Online Technical Appendix p. 10 (PDF 43), proof of Lemma 4; Table 2, p. 33 (PDF 33)

import Mathlib
import Definitions.Def_NonExclEncroach_Channels_Model

namespace NonExclEncroach.Channels

theorem lemma_4_thresholds (θ : ℝ) (h0 : 0 < θ) (h1 : θ < 1) :
    c0 θ ≤ c1 θ ∧ c1 θ ≤ c2 θ ∧ c2 θ ≤ c3 θ := by sorry

end NonExclEncroach.Channels
