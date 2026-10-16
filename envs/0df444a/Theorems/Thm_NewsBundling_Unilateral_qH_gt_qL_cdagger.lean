-- Prove2me | Theorems.Thm_NewsBundling_Unilateral_qH_gt_qL_cdagger
-- name    : NewsBundling.Unilateral.qH_gt_qL_cdagger
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:06:53.110032+00:00
-- url     : https://prove2.me/theorems/6a617e2b-d3c3-4b99-a855-5ae783f808d5
-- title:
--   §4.2, p. 12 — branch maximizers and threshold $c^\dagger$
-- statement:
--   Under Table 1's assumptions, define the two quadratic expressions
--
--   $$\pi_{1L}(q,c)=\phi_1q-\frac{cq^2}{2},\qquad \pi_{1H}(q,c)=\frac{\phi_1\Lambda(1-q)}{1-\Lambda}+\frac{\beta(q-\Lambda)}{1-\Lambda}-\frac{cq^2}{2}.$$
--
--   Their respective maximizers over real $q$ are $q_L(c)=\phi_1/c$ and $q_H(c)=(\beta-\Lambda\phi_1)/(c(1-\Lambda))$. They satisfy $q_H(c)>q_L(c)$. The threshold $c^\dagger=(\beta+\phi_1(1-2\Lambda))/(2\Lambda(1-\Lambda))$ makes the maximized branch profits equal:
--
--   $$\pi_{1L}(q_L(c^\dagger),c^\dagger)=\pi_{1H}(q_H(c^\dagger),c^\dagger).$$
--
--   These candidates and their crossover organize the publisher's quality choice.
--
--   **Formalization Note** The branch maximizers here are over all real qualities, as in the paper's displayed argmax expressions. The feasible game quality remains in $[0,1]$.
-- source:
--   de Cornière & Sarvary, Social Media and News: Content Bundling and News Quality, TSE Working Paper n° 1152 (August 2021), p. 12, §4.2, displayed definitions of π1L, π1H, qL, qH and c†

import Mathlib
import Definitions.Def_NewsBundling_Unilateral_Setting

namespace NewsBundling.Unilateral

/-- Section 4.2, p. 12: the two unrestricted branch maximizers and their crossover. -/
theorem qH_gt_qL_cdagger (β φ0 φ1 c Λ : ℝ)
    (h : StandingAssumptions β φ0 φ1 c Λ) :
    (∀ q : ℝ, pi1L φ1 q c ≤ pi1L φ1 (qL φ1 c) c) ∧
    (∀ q : ℝ, pi1H β φ1 Λ q c ≤ pi1H β φ1 Λ (qH β φ1 c Λ) c) ∧
    qL φ1 c < qH β φ1 c Λ ∧
    pi1L φ1 (qL φ1 (cdagger β φ1 Λ)) (cdagger β φ1 Λ) =
      pi1H β φ1 Λ (qH β φ1 (cdagger β φ1 Λ) Λ) (cdagger β φ1 Λ) := by sorry

end NewsBundling.Unilateral
