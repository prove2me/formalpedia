-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_signed_interval_packing
-- name    : OAI.AsymptoticallyMinimalLittlewood.Packing.signed_interval_packing
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:46:43.073784+00:00
-- url     : https://prove2.me/theorems/064c6d4d-e310-43dc-b133-03a15efaff1a
-- title:
--   Disjoint signed arcs around integer-linear phases on the circle
-- statement:
--   Let $\mathbb{T}=\mathbb{R}/\mathbb{Z}$ be the circle. For $c\in\mathbb{T}$ and $\ell\in\mathbb{R}$ let
--   $$I(c,\ell)=\{c+s\bmod 1:\ s\in\mathbb{R},\ |s|\le\ell/2\}$$
--   be the closed arc of length $\ell$ centred at $c$ (all of $\mathbb{T}$ if $\ell\ge1$, empty if $\ell<0$). For $\theta=(\theta_1,\dots,\theta_m)\in\mathbb{T}^m$ and an integer vector $b\in\mathbb{Z}^m$ write $\langle b,\theta\rangle=\sum_k b_k\theta_k\in\mathbb{T}$.
--
--   Let $r\ge2$ and $m\ge0$ be integers and let $a=(a_{ik})\in\mathbb{Z}^{r\times m}$ be an integer matrix whose rows $a_0,\dots,a_{r-1}$ are nonzero and pairwise non-proportional over $\mathbb{Q}$: $a_l\neq c\,a_j$ for all $j\neq l$ and $c\in\mathbb{Q}$. Let $w_0,\dots,w_{r-1}>0$ be widths with
--   $$2\sum_{i=0}^{r-1}w_i<1 .$$
--   Then there exist an integer $H\ge1$ and points $\theta_1,\dots,\theta_H\in\mathbb{T}^m$ such that the $2rH$ arcs
--   $$I\big(\epsilon\,\langle a_i,\theta_h\rangle,\ w_i/H\big),\qquad\epsilon\in\{+1,-1\},\ 0\le i<r,\ 1\le h\le H,$$
--   are pairwise disjoint: the arcs with labels $(\epsilon,i,h)\neq(\epsilon',j,h')$ do not intersect.
--
--   The arcs have total length $\sum_{\epsilon,i,h}w_i/H=2\sum_iw_i$, so the hypothesis is the volume condition in strict form. The theorem says that, using sufficiently many phase vectors, the signed frequencies $\pm\langle a_i,\theta_h\rangle$ of a fixed family of integer frequency vectors can be spread over the circle with prescribed row-dependent clearances. Through a version for arbitrary finite index sets, it is used in the construction of flat Littlewood polynomials to place the signed frequencies of an auxiliary trigonometric packet in disjoint arcs whose lengths are proportional to the corresponding curvatures.
--
--   **Formalization Note** The circle is `UnitAddCircle`, $I(c,\ell)$ is `circleInterval`, the sign $\epsilon$ is a Boolean with `signedCircle true z = z` and `signedCircle false z = -z`, and $\langle a_i,\theta_h\rangle$ is the sum of the integer multiples $a_{ik}\cdot\theta_{h,k}$ in the additive circle; the points are indexed by `Fin H`. The hypotheses on the rows are stated for the rows viewed as vectors of rationals.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/IntervalPacking.lean#L307-L376

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank
import Definitions.Def_OAI_Analysis_Littlewood_Chunks
import Definitions.Def_OAI_Analysis_Littlewood_DependentMoments
import Definitions.Def_OAI_Analysis_Littlewood_SlotGraph
import Definitions.Def_OAI_Analysis_Littlewood_SlotParameters
import Definitions.Def_OAI_Analysis_Littlewood_IntervalPacking

open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Packing
open scoped BigOperators
open Finset

theorem OAI.AsymptoticallyMinimalLittlewood.Packing.signed_interval_packing {r m : ℕ} (hr : 2≤r)
    (a : Fin r → Fin m → ℤ)
    (ha : ∀ j, (fun k ↦ (a j k : ℚ))≠0)
    (hnp : ∀ j l, j≠l → ∀ c : ℚ,
      (fun k ↦ (a l k : ℚ))≠c • (fun k ↦ (a j k : ℚ)))
    (w : Fin r → ℝ) (hw : ∀ i, 0<w i) (hs : 2*∑ i, w i<1) :
    ∃ H : ℕ, 1≤H ∧ ∃ θ : Fin H → Fin m → UnitAddCircle,
      ∀ e f : Bool, ∀ i j : Fin r, ∀ h v : Fin H, (e,i,h)≠(f,j,v) →
        Disjoint (circleInterval (signedCircle e (∑ k, a i k • θ h k)) (w i/H))
          (circleInterval (signedCircle f (∑ k, a j k • θ v k)) (w j/H)) := by sorry
