-- Prove2me | Theorems.Thm_OPG37364_opg_negative_corollary
-- name    : OPG37364.opg_negative_corollary
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-08T04:51:44.783465+00:00
-- url     : https://prove2.me/theorems/8f2b19ed-a334-4b00-9432-f3511532866f
-- title:
--   Bounded-degree counterexamples at every girth
-- statement:
--   For every integer $g\ge3$, there exists a finite connected graph $G$ with at least two vertices such that
--
--   $$
--   G\text{ is $14$-regular},\qquad
--   \operatorname{girth}(G)\ge g,\qquad
--   G\text{ has no matching cut}.
--   $$
--
--   Thus these graphs have average degree $14<15$ and give the substantive negative answer to the intended OPG-37364 question, independently of the literal one-vertex boundary ambiguity.
-- source:
--   Feghali--Lucke--Paulusma--Ries, Matching Cuts in Graphs of High Girth and H-Free Graphs, Algorithmica 87 (2025), 1199-1221, https://doi.org/10.1007/s00453-025-01318-8, immediate consequence of Lemma 5; the paper's Section 1.2 explicitly identifies the negative answer to the Open Problem Garden question

import Definitions.Def_opg37364_matching_cuts

namespace OPG37364

/-- Substantive negative answer to the intended OPG question, avoiding the
literal one-vertex boundary case: average degree is exactly fourteen and no
matching cut exists at arbitrarily large girth. -/
theorem opg_negative_corollary :
    ∀ g : ℕ, 3 ≤ g →
      ∃ n : ℕ, 2 ≤ n ∧ ∃ G : SimpleGraph (Fin n),
        IsConnected G ∧ IsRegularOfDegree G 14 ∧ HasGirthAtLeast G g ∧
        ¬ HasMatchingCut G := by sorry

end OPG37364
