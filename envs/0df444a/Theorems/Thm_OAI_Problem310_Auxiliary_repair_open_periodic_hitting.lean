-- Prove2me | Theorems.Thm_OAI_Problem310_Auxiliary_repair_open_periodic_hitting
-- name    : OAI.Problem310.Auxiliary.repair_open_periodic_hitting
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:21:15.399883+00:00
-- url     : https://prove2.me/theorems/e3fb69eb-8673-4512-b982-9e860013ab19
-- title:
--   Repairing an open periodic test set into a hitting set for all normalized progressions
-- statement:
--   Write $\lambda$ for Lebesgue measure on $\mathbb{R}$, call $H\subseteq\mathbb{R}$ *1-periodic* if $x+1\in H\iff x\in H$ for all $x\in\mathbb{R}$, and for $B\subseteq\mathbb{R}$, $N\subseteq\mathbb{N}$ and a real sequence $a=(a_n)_{n\in\mathbb{N}}$ let
--   $$\mathcal X(B,N,a)=\bigl\{x\in\mathbb{R}:\ \exists\,t\in[1,2]\ \ \forall n\in N,\ \ x+t\,a_n\notin B\bigr\}$$
--   be the set of exceptional centers.
--
--   **Theorem.** Assume:
--
--   1. $B\subseteq\mathbb{R}$ is open and 1-periodic;
--   2. $N\subseteq\mathbb{N}$, and every $n\in N$ satisfies $n\ge 1$;
--   3. $a_n\to 0$ as $n\to\infty$;
--   4. $c\in[0,\infty]$ satisfies $\lambda\bigl(B\cap[0,1]\bigr)+\lambda\bigl(\mathcal X(B,N,a)\cap[0,1]\bigr)\le c$;
--   5. $\varepsilon>0$.
--
--   Then there is an open, 1-periodic set $H\subseteq\mathbb{R}$ with $\lambda(H\cap[0,1])\le c+\varepsilon$ that is hit by every normalized progression:
--   $$\forall x\in\mathbb{R}\ \ \forall t\in[1,2]\ \ \exists\,n\in\mathbb{N},\ n\ge 1:\quad x+t\,a_n\in H .$$
--
--   This is the deterministic repair step of a probabilistic construction: if an open periodic test set $B$ has small density and its exceptional centers also have small density, then a genuine hitting set costs only $\varepsilon$ more. For $a_n=2^{-n}$, the complement $[0,1]\setminus H$ is a compact set of measure at least $1-(c+\varepsilon)$ that contains no set of the form $\{x+t\,2^{-n}: n\ge 1\}$ with $x\in\mathbb{R}$ and $t\in[1,2]$.
--
--   **Formalization Note** The index $n$ in the conclusion is any natural number $n\ge 1$; it need not belong to $N$. Measures and $c$ are extended nonnegative reals, and $\varepsilon$ enters as `ENNReal.ofReal ε`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/ExceptionalCenters.lean#L133-L167

import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterRouteExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ExceptionalCenters

open OAI OAI.Problem310 OAI.Problem310.Auxiliary
open Set Filter Topology
open Set Filter Topology MeasureTheory

theorem OAI.Problem310.Auxiliary.repair_open_periodic_hitting
    (B : Set ℝ) (hBo : IsOpen B)
    (hBp : ∀ x : ℝ, x + 1 ∈ B ↔ x ∈ B)
    (N : Set ℕ) (hN : ∀ n ∈ N, 1 ≤ n)
    (a : ℕ → ℝ) (ha : Tendsto a atTop (𝓝 0))
    (c : ENNReal)
    (hbound : volume (B ∩ Icc (0 : ℝ) 1) +
      volume (exceptionalCenters B N a ∩ Icc (0 : ℝ) 1) ≤ c)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ H : Set ℝ, IsOpen H ∧
      (∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) ∧
      volume (H ∩ Icc (0 : ℝ) 1) ≤ c + ENNReal.ofReal ε ∧
      ∀ x t : ℝ, t ∈ Icc (1 : ℝ) 2 →
        ∃ n : ℕ, 1 ≤ n ∧ x + t * a n ∈ H := by sorry
