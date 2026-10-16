-- Prove2me | Theorems.Thm_OAI_Problem310_FirstDefault_cylinder_iff_chooseChild
-- name    : OAI.Problem310.FirstDefault.cylinder_iff_chooseChild
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:32:13.985623+00:00
-- url     : https://prove2.me/theorems/3361b4b2-b310-426e-a036-b93b2bc60460
-- title:
--   Path cylinders are exactly the events that first-success routing follows a prescribed path
-- statement:
--   Let $M,d\in\mathbb{N}$ and let $\Omega$ be an arbitrary set. An *address* is a pair $(P,j)$ of a finite word $P$ over the alphabet $\{0,1,\dots,M\}$ and a letter $j\in\{0,\dots,M-1\}$; suppose that to every address a Boolean function $S_{P,j}:\Omega\to\{\mathrm{true},\mathrm{false}\}$ is assigned (the selector of child $j$ at node $P$). For a bit vector $s=(s_0,\dots,s_{M-1})$ let $\operatorname{ch}(s)\in\{0,\dots,M\}$ be the least index $j$ with $s_j=\mathrm{true}$, and $\operatorname{ch}(s)=M$ (the default child) if there is none.
--
--   Let $f=(f_0,\dots,f_{d-1})$ be a sequence of nondefault letters $f_k\in\{0,\dots,M-1\}$, and write $f_{<k}=(f_0,\dots,f_{k-1})$ for its prefix of length $k$. The *path cylinder* of $f$ is
--   $$C_S(f)=\bigl\{\omega\in\Omega:\ \bigl(S_{f_{<k},j}(\omega)=\mathrm{true}\iff j=f_k\bigr)\ \text{ for all } k<d \text{ and all } j\le f_k\bigr\},$$
--   i.e. at each node $f_{<k}$ the selectors $j<f_k$ fail and the selector $f_k$ succeeds.
--
--   **Theorem.** For every $\omega\in\Omega$,
--
--   $$\omega\in C_S(f)\iff \operatorname{ch}\bigl(S_{f_{<k},0}(\omega),\dots,S_{f_{<k},M-1}(\omega)\bigr)=f_k\quad\text{for every }k\in\{0,\dots,d-1\}.$$
--
--   In words, the cylinder is exactly the event that first-success routing, started at the root, selects the prescribed child $f_k$ at each prescribed node $f_{<k}$. It turns the event "the route follows the nondefault path $f$" into a finite conjunction of conditions on individual selector bits, which is how the probability that a route never takes the default child is computed.
--
--   **Formalization Note** Addresses are `List (Fin (M + 1)) × Fin M`, the path is `f : Fin d → Fin M`, the node $f_{<k}$ is `pathPrefix f k`, and the cylinder `cylinder S f` is defined through the tests `(k : Fin d) × Fin ((f k).val + 1)` with required bits `decide (j = f k)`. The right-hand side compares `OrderedRouting.chooseChild`, valued in `Fin (M + 1)`, with `(f k).castSucc`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/FirstDefaultSelection.lean#L13-L43

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

open OAI OAI.Problem310 OAI.Problem310.FirstDefault
universe u_Ω u_ι u_X u_Y

theorem OAI.Problem310.FirstDefault.cylinder_iff_chooseChild {M d : ℕ} {Ω : Type u_Ω}
    (S : Address M → Ω → Bool) (f : Path M d) (ω : Ω) :
    ω ∈ cylinder S f ↔ ∀ k : Fin d,
      OrderedRouting.chooseChild (fun j => S (pathPrefix f k, j) ω) = (f k).castSucc := by sorry
