-- Prove2me | Theorems.Thm_HadwigerConj_delcourt_postle_colorable
-- name    : HadwigerConj.delcourt_postle_colorable
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-01T00:02:33.573052+00:00
-- url     : https://prove2.me/theorems/770d8ed0-ec13-45e4-839c-2815a1803783
-- title:
--   Delcourt–Postle: no $K_t$ minor $\Rightarrow$ $O(t\log\log t)$-colourable
-- statement:
--   There is an absolute constant $C$ such that for every $t\ge 3$, every finite graph with no $K_t$ minor is colourable with $\lceil C\,t\log\log t\,\rceil$ colours:
--
--   $$K_t\not\preceq G\ \Longrightarrow\ \chi(G)=O(t\log\log t).$$
--
--   This is the current best general upper bound (Norin–Postle–Song 2023, Delcourt–Postle 2024).
--
--   **Formalization Note** $\log$ is the natural logarithm; $t\ge 3$ ensures $\log\log t>0$.
-- source:
--   Wikipedia, "Hadwiger conjecture (graph theory)", https://en.wikipedia.org/wiki/Hadwiger_conjecture_(graph_theory), section “Special cases and partial results” (“A sequence of improvements to this bound have led to a proof of O(t log log t)-colorability for graphs without K_t minors”, citing Delcourt & Postle (2024); Norin, Postle & Song (2023))

import Mathlib
import Definitions.Def_HadwigerConj_Defs

namespace HadwigerConj
theorem delcourt_postle_colorable :
    ∃ C : ℝ, ∀ t : ℕ, 3 ≤ t → ∀ (V : Type) [Finite V] (G : SimpleGraph V),
      ¬ HasCompleteMinor G t → G.Colorable ⌈C * t * Real.log (Real.log t)⌉₊ := by sorry
end HadwigerConj
