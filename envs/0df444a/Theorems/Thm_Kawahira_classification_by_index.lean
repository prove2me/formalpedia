-- Prove2me | Theorems.Thm_Kawahira_classification_by_index
-- name    : Kawahira.classification_by_index
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T18:30:33.135834+00:00
-- url     : https://prove2.me/theorems/8b3fc9c4-456d-48ca-8839-09bac2bc6b17
-- title:
--   Proposition 4 — classification of fixed points by $\operatorname{Re}\iota$
-- statement:
--   Let $\lambda \in \mathbb{C}$ with $\lambda \neq 1$, and put $\iota = \frac{1}{1-\lambda}$. Then
--   $$|\lambda| < 1 \iff \operatorname{Re}\iota > \tfrac12, \qquad |\lambda| = 1 \iff \operatorname{Re}\iota = \tfrac12, \qquad |\lambda| > 1 \iff \operatorname{Re}\iota < \tfrac12 .$$
--
--   Combined with Proposition 3, this says that a fixed point with multiplier $\lambda \neq 1$ is attracting, indifferent or repelling exactly according to whether the real part of its holomorphic index is greater than, equal to, or less than $1/2$. The line $\operatorname{Re}\iota = 1/2$ in the index plane is the image of the unit circle under $\lambda \mapsto (1-\lambda)^{-1}$; this is the coincidence that lets the critical line of the zeta function be read as a dynamical condition.
--
--   **Formalization Note** The statement is purely about complex numbers — no dynamics, no analyticity — which isolates the Möbius-geometry content of the paper's Proposition 4.
-- source:
--   Tomoki Kawahira, "The Riemann Hypothesis and Holomorphic Index in Complex Dynamics", Experimental Mathematics (2016), DOI: 10.1080/10586458.2016.1217443

import Definitions.Def_Kawahira_zeta

open Complex Topology

namespace Kawahira

theorem classification_by_index (lam : ℂ) (h : lam ≠ 1) :
    (‖lam‖ < 1 ↔ 1 / 2 < (1 / (1 - lam)).re) ∧
      (‖lam‖ = 1 ↔ (1 / (1 - lam)).re = 1 / 2) ∧
      (1 < ‖lam‖ ↔ (1 / (1 - lam)).re < 1 / 2) := by sorry

end Kawahira
