-- Prove2me | Theorems.Thm_OAI_RepeatedLocalization_cellSet_subset_initialCube
-- name    : OAI.RepeatedLocalization.cellSet_subset_initialCube
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T19:40:48.181134+00:00
-- url     : https://prove2.me/theorems/17ce6b85-e03a-4b18-9d74-a7419c73e1b2
-- title:
--   Every dyadic cell lies in the initial cube
-- statement:
--   Let $n\ge1$ and let $C_n=\big[-\tfrac{1}{2\sqrt n},\tfrac{1}{2\sqrt n}\big)^n\subseteq\mathbb{R}^n$ be the initial cube. A dyadic cell is a pair $Q=(J,k)$ of a level $J\in\mathbb{N}$ and an index vector $k\in\{0,1,\dots,2^J-1\}^n$, and its box is
--
--   $$
--   B_Q=\Big\{z\in\mathbb{R}^n:\ -\frac{1}{2\sqrt n}+\frac{k_i}{\sqrt n\,2^J}\le z_i<-\frac{1}{2\sqrt n}+\frac{k_i+1}{\sqrt n\,2^J}\ \text{ for all } i\Big\}.
--   $$
--
--   Then for every dyadic cell $Q$,
--
--   $$
--   B_Q\subseteq C_n .
--   $$
--
--   So every cell of the dyadic tree lies inside the support of the cube prior, the uniform distribution on $C_n$. As a consequence, the prior mass of a cell is a plain ratio of volumes, and the uniform law on a cell is the cube prior conditioned on that cell.
--
--   **Formalization Note** The sets are `cellSet Q` and `initialCube n`; cells are elements of `Cell n`, a level together with an index map `Fin n -> Fin (2^J)`. The statement carries the hypothesis `0 < n`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Localization/Cells.lean#L38-L50

import Mathlib
import Definitions.Def_GaussianFiniteEntropy
import Definitions.Def_OAI_Probability_Localization_Experiment
import Definitions.Def_OAI_Probability_Localization_Cells

open OAI OAI.RepeatedLocalization
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

theorem OAI.RepeatedLocalization.cellSet_subset_initialCube {n : ℕ} (hn : 0 < n) (Q : Cell n) :
    cellSet Q ⊆ initialCube n := by sorry
