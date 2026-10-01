-- Prove2me | Theorems.Thm_HadwigerConj_kostochka_thomason_colorable
-- name    : HadwigerConj.kostochka_thomason_colorable
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T23:57:18.799632+00:00
-- url     : https://prove2.me/theorems/bc508126-274c-4b1a-a0e9-8e2df2c2b34e
-- title:
--   Kostochka–Thomason: no $K_t$ minor $\Rightarrow$ $O(t\sqrt{\log t})$-colourable
-- statement:
--   There is an absolute constant $C$ such that for every $t\ge 1$, every finite graph with no $K_t$ minor is colourable with $\lceil C\,t\sqrt{\log t}\,\rceil$ colours:
--
--   $$K_t\not\preceq G\ \Longrightarrow\ \chi(G)=O\big(t\sqrt{\log t}\big).$$
--
--   It follows from the Kostochka–Thomason bound on the average degree of graphs with no $K_t$ minor (Theorem 3.6 of the survey) via degeneracy; the survey notes this was long the best bound for large $t$.
--
--   **Formalization Note** $\log$ is the natural logarithm; the colour count is the ceiling (as a natural number) of $C t\sqrt{\log t}$.
-- source:
--   P. Seymour, "Hadwiger's conjecture" (survey), in: Open Problems in Mathematics, Springer, 2016 (uploaded PDF `paper.pdf`), Section 3, paragraph after Theorem 3.12 (p. 7: “every graph with no K_t minor has degeneracy at most O(t(log t)^{1/2}), and therefore chromatic number at most the same”); Wikipedia, "Hadwiger conjecture (graph theory)", https://en.wikipedia.org/wiki/Hadwiger_conjecture_(graph_theory), section “Special cases and partial results”

import Mathlib
import Definitions.Def_HadwigerConj_Defs

namespace HadwigerConj
theorem kostochka_thomason_colorable :
    ∃ C : ℝ, ∀ t : ℕ, 1 ≤ t → ∀ (V : Type) [Finite V] (G : SimpleGraph V),
      ¬ HasCompleteMinor G t → G.Colorable ⌈C * t * Real.sqrt (Real.log t)⌉₊ := by sorry
end HadwigerConj
