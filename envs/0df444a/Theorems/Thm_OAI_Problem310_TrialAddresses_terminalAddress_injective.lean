-- Prove2me | Theorems.Thm_OAI_Problem310_TrialAddresses_terminalAddress_injective
-- name    : OAI.Problem310.TrialAddresses.terminalAddress_injective
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:43:35.279779+00:00
-- url     : https://prove2.me/theorems/9ebad396-03a8-4346-a902-14280eb0aa29
-- title:
--   Injectivity of adaptive terminal addresses under resolution refinement
-- statement:
--   For $\beta\in\mathbb{N}$ and $y\in\mathbb{R}$ let $\kappa_\beta(y)=\lfloor 2^{\beta+2}(y-\lfloor y\rfloor)\rfloor\in\{0,\dots,2^{\beta+2}-1\}$ be the index of the cell containing $y$ in the $1$-periodic grid of mesh $2^{-\beta-2}$.
--
--   Let $I$ be a set of trials, $C$ a set of *children* and $L$ a set of *leaves*. Each trial $i$ tests a child $\mathrm{child}(i)\in C$ at a dyadic scale index $n(i)\in\mathbb{N}$ and reads the terminal table of a leaf $\mathrm{leaf}(i)\in L$. Children carry resolutions $b:C\to\mathbb{N}$ and leaves carry resolutions $B:L\to\mathbb{N}$; a terminal address is a pair $(\ell,m)$ with $\ell\in L$ and $m\in\{0,\dots,2^{B(\ell)+2}-1\}$. For $x,t\in\mathbb{R}$ trial $i$ reads the address
--
--   $$\theta(i)=\Big(\mathrm{leaf}(i),\ \kappa_{B(\mathrm{leaf}(i))}\big(x+t\,2^{-n(i)}\big)\Big).$$
--
--   **Theorem.** Assume $1\le t\le 2$ and, for all trials $i,j$:
--
--   1. $3\le n(i)\le b(\mathrm{child}(i))$;
--   2. $b(\mathrm{child}(i))\le B(\mathrm{leaf}(i))$ (the terminal resolution refines the child's resolution);
--   3. $\mathrm{leaf}(i)=\mathrm{leaf}(j)$ implies $\mathrm{child}(i)=\mathrm{child}(j)$ (a leaf lies below only one tested child);
--   4. $i\mapsto(\mathrm{child}(i),n(i))$ is injective.
--
--   Then $\theta$ is injective.
--
--   No other condition is imposed on the leaf assignment; in the application the leaf of a trial is found by routing and may depend arbitrarily on all selector tables, and the theorem is applied separately for each selector outcome. It guarantees that distinct trials read distinct terminal cells, so their terminal bits are independent.
--
--   **Formalization Note** The map $\theta$ is `trialAddress B leaf n x t`, with values in `GridAddress B = Σ ℓ : L, Fin (2 ^ (B ℓ + 2))`; $\kappa_\beta$ is `dyadicKey β`. The types $I$, $C$, $L$ are arbitrary.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/TrialAddresses.lean#L78-L104

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

theorem OAI.Problem310.TrialAddresses.terminalAddress_injective {I : Type u_I} {C : Type u_C} {L : Type u_L}
    (child : I → C) (n : I → ℕ) (leaf : I → L)
    (b : C → ℕ) (B : L → ℕ) (x t : ℝ)
    (htlo : 1 ≤ t) (hthi : t ≤ 2)
    (hnlo : ∀ i, 3 ≤ n i) (hnhi : ∀ i, n i ≤ b (child i))
    (hrefine : ∀ i, b (child i) ≤ B (leaf i))
    (hbranch : ∀ i j, leaf i = leaf j → child i = child j)
    (hpair : Function.Injective (fun i => (child i, n i))) :
    Function.Injective (trialAddress B leaf n x t) := by sorry
