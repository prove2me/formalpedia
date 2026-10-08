-- Prove2me | Theorems.Thm_MultistageStab_Value_display_10
-- name    : MultistageStab.Value.display_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:13.678495+00:00
-- url     : https://prove2.me/theorems/06cecc58-0586-4259-8715-0846619eaf4c
-- title:
--   (10), proof of Theorem 2.1, p. 5 — sup_{x∈M_t(ū)} d(x, M_t(ũ)) ≤ l_t‖ū − ũ‖
-- statement:
--   Consider the multistage data of program (1) and, for each stage $t = 2,\dots,T$, the set-valued map
--   $$M_t(u) = \{x \in \mathbb R^{m_t} : A_{t,0}x = u,\ x \in X_t\},\qquad u \in \mathbb R^{n_t},$$
--   where $X_t$ is the polyhedral cone of stage $t$. Assume complete fixed recourse (A1): $A_{t,0}X_t = \mathbb R^{n_t}$ for $t = 2,\dots,T$. Then for every $t = 2,\dots,T$ there is a constant $l_t > 0$ such that
--   $$\sup_{x \in M_t(\bar u)} d\big(x, M_t(\tilde u)\big) \le l_t\,\|\bar u - \tilde u\|\qquad\text{for all } \bar u,\tilde u \in \mathbb R^{n_t},$$
--   where $d(x,A)$ is the Euclidean distance of $x$ to the set $A$.
--
--   This is the Lipschitz continuity of the polyhedral maps $M_t$ in the Hausdorff sense; it is what lets a feasible policy for one input be moved to a nearby feasible policy for another input with a controlled error.
--
--   **Formalization Note** The supremum is stated pointwise, for every $x \in M_t(\bar u)$. The sets $M_t(\tilde u)$ are nonempty by (A1), so the distance is not the junk value of an empty set.
-- source:
--   Heitsch, Römisch & Strugarek, Stability of multistage stochastic programs, author manuscript (edoc.hu-berlin.de, c. 2005), p. 5, proof of Theorem 2.1, (10)

import Mathlib
import Definitions.Def_MultistageStab_Value_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MultistageStab.Value

theorem display_10 (D : Data) (hA1 : CompleteRecourse D) :
    ∀ t ∈ Finset.Icc 2 D.T, ∃ l : ℝ, 0 < l ∧
      ∀ ubar util : E (D.n t), ∀ x ∈ {x : E (D.m t) | x ∈ Xc D t ∧ D.A₀ t x = ubar},
        Metric.infDist x {x : E (D.m t) | x ∈ Xc D t ∧ D.A₀ t x = util} ≤ l * ‖ubar - util‖ := by sorry

end MultistageStab.Value
