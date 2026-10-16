-- Prove2me | Theorems.Thm_OAI_Problem310_TrialAddresses_trialAddress_injective
-- name    : OAI.Problem310.TrialAddresses.trialAddress_injective
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:42:58.606813+00:00
-- url     : https://prove2.me/theorems/b873670c-2642-4fa3-bcea-c2f63a790a08
-- title:
--   Distinct table-index pairs give distinct dyadic trial addresses
-- statement:
--   For $\beta\in\mathbb{N}$ and $y\in\mathbb{R}$ let $\kappa_\beta(y)=\lfloor 2^{\beta+2}(y-\lfloor y\rfloor)\rfloor\in\{0,\dots,2^{\beta+2}-1\}$ be the index of the cell containing $y$ in the $1$-periodic grid of mesh $2^{-\beta-2}$.
--
--   Let $E$ be a set of *table names* with resolutions $b:E\to\mathbb{N}$; a *grid address* is a pair $(e,m)$ with $e\in E$ and $m\in\{0,\dots,2^{b(e)+2}-1\}$. Let $I$ be a set of *trials*, and let $\mathrm{edge}:I\to E$ assign to each trial the table it reads and $n:I\to\mathbb{N}$ its dyadic scale index. For $x,t\in\mathbb{R}$, trial $i$ reads the table $\mathrm{edge}(i)$ at the point $x+t\,2^{-n(i)}$, i.e. at the address
--
--   $$\theta(i)=\Big(\mathrm{edge}(i),\ \kappa_{b(\mathrm{edge}(i))}\big(x+t\,2^{-n(i)}\big)\Big).$$
--
--   **Theorem.** Assume $1\le t\le 2$, $3\le n(i)\le b(\mathrm{edge}(i))$ for every $i\in I$, and that $i\mapsto(\mathrm{edge}(i),n(i))$ is injective. Then $\theta:I\to\{\text{grid addresses}\}$ is injective.
--
--   Thus trials with different (table, scale) pairs always read different table cells, for every center $x$ and every normalized scale $t\in[1,2]$, with no exceptional centers near grid boundaries. In a random table with independent entries, the bits read by distinct trials are therefore independent; this is the freshness input for exact miss-probability computations.
--
--   **Formalization Note** Grid addresses are the dependent pairs `GridAddress b = Σ e : E, Fin (2 ^ (b e + 2))`, $\kappa_\beta$ is `dyadicKey β`, and $\theta$ is `trialAddress b edge n x t`. The types $I$ and $E$ are arbitrary (not necessarily finite).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/TrialAddresses.lean#L59-L76

import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterRouteExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ExceptionalCenters
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFailureBound
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteLabelMeasures
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RandomSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefaultSelection
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteLocalPredicate
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowData
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_StableRoutingBridge
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowExceptionalTransfer
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_TrialAddresses

open OAI OAI.Problem310 OAI.Problem310.TrialAddresses
universe u_E u_I u_C u_L
open GridSeparation

theorem OAI.Problem310.TrialAddresses.trialAddress_injective {I : Type u_I} {E : Type u_E} (b : E → ℕ) (edge : I → E)
    (n : I → ℕ) (x t : ℝ) (htlo : 1 ≤ t) (hthi : t ≤ 2)
    (hnlo : ∀ i, 3 ≤ n i) (hnhi : ∀ i, n i ≤ b (edge i))
    (hpair : Function.Injective (fun i => (edge i, n i))) :
    Function.Injective (trialAddress b edge n x t) := by sorry
