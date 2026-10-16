-- Prove2me | Theorems.Thm_OAI_Problem310_Auxiliary_periodic_hitting_of_raw_construction
-- name    : OAI.Problem310.Auxiliary.periodic_hitting_of_raw_construction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T05:01:18.004303+00:00
-- url     : https://prove2.me/theorems/bce4798a-644d-4066-81fc-ad08f777e2b6
-- title:
--   Open periodic dyadic hitting set from a raw random periodic construction
-- statement:
--   Let $\Omega$ be a finite set whose singletons are measurable, let $\mu$ be a probability measure on $\Omega$, write $\mathbb{E}_\mu$ for expectation with respect to $\mu$, and let $\lambda$ denote Lebesgue outer measure on $\mathbb{R}$ (Lebesgue measure on measurable sets). A set $B\subseteq\mathbb{R}$ is *$1$-periodic* if $x+1\in B\iff x\in B$ for every $x\in\mathbb{R}$. Let $N\subseteq\mathbb{N}$ be a set of indices with $n\ge1$ for every $n\in N$.
--
--   For $B\subseteq\mathbb{R}$, the *exceptional centers* of $B$ relative to $N$ are the points from which some dilate of the dyadic sequence, indexed by $N$, misses $B$:
--
--   $$\mathcal{E}_N(B)=\big\{x\in\mathbb{R}:\ \exists\,t\in[1,2]\ \ \forall n\in N:\ x+t\,2^{-n}\notin B\big\}.$$
--
--   **Theorem.** Let $p>0$ and, for each $\omega\in\Omega$, let $B_\omega\subseteq\mathbb{R}$ be a $1$-periodic set; neither openness nor measurability of $B_\omega$ is assumed. Let $G\subseteq\mathbb{R}$ be a Borel set. Assume
--
--   $$\lambda(G^{c}\cap[0,1])\le p,\qquad\mathbb{E}_\mu\big[\lambda(B_\omega\cap[0,1])\big]\le p,\qquad \mu\big(\{\omega:\ x\in\mathcal{E}_N(B_\omega)\}\big)\le 2p\ \text{ for every } x\in G.$$
--
--   Then there is an open set $H\subseteq\mathbb{R}$ with $x+1\in H\iff x\in H$ for all $x\in\mathbb{R}$ such that
--
--   $$\lambda\big(H\cap[0,1]\big)\le 6p\qquad\text{and}\qquad\forall x\in\mathbb{R}\ \ \forall t\in[1,2]\ \ \exists n\ge1:\ x+t\,2^{-n}\in H.$$
--
--   Here $n$ ranges over all integers $n\ge1$, not only over $N$.
--
--   This is the complete analytic interface for a finite random periodic construction: the random set may be raw, and the hypotheses are exactly a bound on its mean density, a set of bad centers of measure at most $p$ per period, and a pointwise bound on the probability that a good center is exceptional.
--
--   **Formalization Note** $\Omega$ is a `Fintype` with a measurable structure in which singletons are measurable, and $\mu$ is a probability measure. Expectations are lower Lebesgue integrals (`lintegral`) of $[0,\infty]$-valued functions, $\lambda$ is `volume`, the real bounds are embedded with `ENNReal.ofReal`, and $\mathcal{E}_N(B)$ is `exceptionalCenters B N` with the sequence $n\mapsto2^{-n}$. Borel measurability of $G$ is `MeasurableSet G`, and on non-measurable sets `volume` is Lebesgue outer measure.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/RawRepair.lean#L15-L59

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
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowTrialAddresses
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteWindowAtom
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicEnvelope

open OAI OAI.Problem310 OAI.Problem310.Auxiliary
universe u_Ω
open Set MeasureTheory

theorem OAI.Problem310.Auxiliary.periodic_hitting_of_raw_construction
    {Ω : Type u_Ω} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℝ) (hp : 0 < p) (B : Ω → Set ℝ)
    (hBp : ∀ ω x, x + 1 ∈ B ω ↔ x ∈ B ω)
    (N : Set ℕ) (hN : ∀ n ∈ N, 1 ≤ n)
    (G : Set ℝ) (hG : MeasurableSet G)
    (hbad : volume (Gᶜ ∩ Icc (0 : ℝ) 1) ≤ ENNReal.ofReal p)
    (hBmean : (∫⁻ ω, volume (B ω ∩ Icc (0 : ℝ) 1) ∂μ) ≤ ENNReal.ofReal p)
    (hgood : ∀ x ∈ G,
      μ {ω | x ∈ exceptionalCenters (B ω) N (fun n => (2 : ℝ)⁻¹ ^ n)}
        ≤ ENNReal.ofReal (2 * p)) :
    ∃ H : Set ℝ, IsOpen H ∧
      (∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) ∧
      volume (H ∩ Icc (0 : ℝ) 1) ≤ ENNReal.ofReal (6 * p) ∧
      ∀ x t : ℝ, t ∈ Icc (1 : ℝ) 2 →
        ∃ n : ℕ, 1 ≤ n ∧ x + t * ((2 : ℝ)⁻¹ ^ n) ∈ H := by sorry
