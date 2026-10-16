-- Prove2me | Theorems.Thm_OAI_Problem310_OrderedRouting_chooseChild_eq_nondefault_iff
-- name    : OAI.Problem310.OrderedRouting.chooseChild_eq_nondefault_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:11:38.991104+00:00
-- url     : https://prove2.me/theorems/3a3ac7f0-5c99-48e2-b0c7-0e63e61b8135
-- title:
--   First-success selection chooses child $i$ iff selector $i$ is the first success
-- statement:
--   Let $M\in\mathbb{N}$. Consider a node of a tree with $M+1$ children labelled $0,1,\dots,M$, where child $M$ is the *default* child, together with a vector of selector bits $S=(S_0,\dots,S_{M-1})\in\{\mathrm{true},\mathrm{false}\}^M$, one for each nondefault child. The *first-success choice* $\operatorname{ch}(S)\in\{0,\dots,M\}$ is the least index $k$ at which the extended sequence $(S_0,\dots,S_{M-1},\mathrm{true})$ is true: it is the first $i<M$ with $S_i=\mathrm{true}$ if there is one, and the default child $M$ otherwise.
--
--   For every nondefault index $i\in\{0,\dots,M-1\}$,
--   $$\operatorname{ch}(S)=i\iff S_i=\mathrm{true}\ \text{ and }\ S_j=\mathrm{false}\ \text{ for all } j<i .$$
--
--   Thus the event that a given nondefault child $i$ is chosen is the explicit cylinder event "selectors $0,\dots,i-1$ fail and selector $i$ succeeds"; for instance, when the selector bits are independent fair coins, child $i$ is chosen with probability $2^{-(i+1)}$. This is the basic step in computing path probabilities for first-success routing.
--
--   **Formalization Note** The choice is `chooseChild S : Fin (M + 1)`, defined with `Fin.find` applied to the predicate `Fin.lastCases true S`; a nondefault index $i$ is embedded in $\{0,\dots,M\}$ by `Fin.castSucc`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/OrderedRouting.lean#L13-L28

import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting

open OAI OAI.Problem310 OAI.Problem310.OrderedRouting
variable {M : ℕ}

theorem OAI.Problem310.OrderedRouting.chooseChild_eq_nondefault_iff (S : Fin M → Bool) (i : Fin M) :
    chooseChild S = i.castSucc ↔ S i = true ∧ ∀ j < i, S j = false := by sorry
