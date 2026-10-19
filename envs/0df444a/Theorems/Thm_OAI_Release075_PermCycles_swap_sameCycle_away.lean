-- Prove2me | Theorems.Thm_OAI_Release075_PermCycles_swap_sameCycle_away
-- name    : OAI.Release075.PermCycles.swap_sameCycle_away
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:50:52.158988+00:00
-- url     : https://prove2.me/theorems/51826054-73cb-4bd0-be76-52a2c60c117e
-- title:
--   Swaps in other colours do not change an orbit
-- statement:
--   Let $f$ be a permutation of a finite set with a colouring that is constant along $f$, i.e. $\mathrm{color}(f z)=\mathrm{color}(z)$. If $a,b$ have colours different from that of $x$, then for every $y$,
--   $$
--   \bigl((a\ b)f\bigr)\text{-same-cycle}(x,y)\iff f\text{-same-cycle}(x,y).
--   $$
--
--   A transposition supported in other colours leaves the orbit of $x$ unchanged.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Planarity.lean#L10-L36

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation
import Definitions.Def_OAI_GroupTheory_Hyperbolic_WordPaths
import Definitions.Def_OAI_GroupTheory_Hyperbolic_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Planarity

open OAI OAI.Release075 OAI.Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

theorem OAI.Release075.PermCycles.swap_sameCycle_away {C : Type*} (f : Perm A) (color : A → C)
    (hcolor : ∀ z, color (f z) = color z) (a b x y : A)
    (ha : color x ≠ color a) (hb : color x ≠ color b) :
    (Equiv.swap a b * f).SameCycle x y ↔ f.SameCycle x y := by sorry
