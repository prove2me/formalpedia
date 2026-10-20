-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_CircleConsequence_extend_to_five
-- name    : OAI.EuclideanRamsey.CircleConsequence.extend_to_five
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T12:28:53.652675+00:00
-- url     : https://prove2.me/theorems/f375d0ad-9a3f-439c-b1f4-de4da917474a
-- title:
--   Extending at most five points on a circle to five points
-- statement:
--   Let $a_0,\dots,a_{s-1}$ be distinct points of $\mathbb R^2$ with $s\le5$, all at distance $r>0$ from $c$. Then there are five distinct points $b_0,\dots,b_4$ with $|b_j-c|=r$ and a map $f$ such that
--   $$
--   b_{f(i)}=a_i\qquad(0\le i<s).
--   $$
--
--   So statements about five concyclic points transfer to fewer points by restriction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/CircleExtension.lean#L62-L95

import Mathlib
import Definitions.Def_EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleInterpolation
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleRows
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleExtension

open OAI OAI.EuclideanRamsey OAI.EuclideanRamsey.CircleConsequence

theorem OAI.EuclideanRamsey.CircleConsequence.extend_to_five {s : ℕ} (a : Fin s → Space 2)
    (hs : s ≤ 5) (ha : Function.Injective a)
    (c : Space 2) (r : ℝ) (hr : 0 < r)
    (hc : ∀ i, dist (a i) c = r) :
    ∃ b : Fin 5 → Space 2, Function.Injective b ∧
      (∀ j, dist (b j) c = r) ∧ ∃ f : Fin s → Fin 5, ∀ i, b (f i) = a i := by sorry
