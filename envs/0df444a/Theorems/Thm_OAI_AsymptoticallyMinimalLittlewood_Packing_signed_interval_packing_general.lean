-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_signed_interval_packing_general
-- name    : OAI.AsymptoticallyMinimalLittlewood.Packing.signed_interval_packing_general
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:48:57.818979+00:00
-- url     : https://prove2.me/theorems/5c033fad-f65c-4f93-aca7-87d28fdec131
-- title:
--   Signed interval packing on the circle for pairwise non-proportional integer frequency vectors
-- statement:
--   Let $I$ and $J$ be finite sets with $I\neq\varnothing$, and write $\mathbb{T}=\mathbb{R}/\mathbb{Z}$ for the unit circle, viewed as an additive group. Let $a=(a_{ik})_{i\in I,\,k\in J}$ be an integer matrix whose rows $a_i\in\mathbb{Z}^J$ are all nonzero and pairwise non-proportional: for $i\neq j$ there is no real number $c$ with $a_{jk}=c\,a_{ik}$ for all $k\in J$. Let $w_i>0$ $(i\in I)$ be weights with $2\sum_{i\in I}w_i<1$.
--
--   For $\theta\in\mathbb{T}^J$ write $\langle a_i,\theta\rangle=\sum_{k\in J}a_{ik}\theta_k\in\mathbb{T}$; for a sign $\sigma\in\{+1,-1\}$ and $z\in\mathbb{T}$, $\sigma z$ is $z$ or $-z$. For $z\in\mathbb{T}$ and $\ell\ge0$ let $\mathcal{I}(z,\ell)=\{z+t \bmod 1 : t\in\mathbb{R},\ |t|\le \ell/2\}$ be the closed arc of length $\ell$ centred at $z$.
--
--   **Theorem.** There exist an integer $H\ge1$ and points $\theta_0,\dots,\theta_{H-1}\in\mathbb{T}^J$ such that for all signs $\sigma,\tau\in\{+1,-1\}$, all $i,j\in I$ and all $h,v\in\{0,\dots,H-1\}$ with $(\sigma,i,h)\neq(\tau,j,v)$,
--   $$
--   \mathcal{I}\Bigl(\sigma\langle a_i,\theta_h\rangle,\ \frac{w_i}{H}\Bigr)\cap\mathcal{I}\Bigl(\tau\langle a_j,\theta_v\rangle,\ \frac{w_j}{H}\Bigr)=\varnothing .
--   $$
--
--   In words, the $2|I|H$ signed values $\pm\langle a_i,\theta_h\rangle$ can be placed on the circle so that the arc of length $w_i/H$ around each of them meets none of the other arcs; in particular the arcs around $\langle a_i,\theta_h\rangle$ and $-\langle a_i,\theta_h\rangle$ are disjoint. The arcs have total length $2\sum_i w_i$, so the hypothesis on the weights is the natural measure constraint. This packing is what separates the stationary points of different chirp modes in the construction of flat Littlewood polynomials; unlike the underlying packing theorem, which needs at least two rows, it also allows a single row ($|I|=1$).
--
--   **Formalization Note** The circle is `UnitAddCircle`, the term $a_{ik}\theta_k$ is the integer scalar multiple `a i k • θ h k`, signs are Booleans with `signedCircle true z = z` and `signedCircle false z = -z`, and $\mathcal{I}(z,\ell)$ is `circleInterval z ℓ`. Non-proportionality is the hypothesis `¬ ∀ k, (a j k : ℝ) = c * (a i k : ℝ)` for all `i ≠ j` and all real `c`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/IntervalPacking.lean#L424-L485

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

theorem OAI.AsymptoticallyMinimalLittlewood.Packing.signed_interval_packing_general {I J : Type} [Fintype I] [Fintype J]
    [Nonempty I] (a : I → J → ℤ) (ha : ∀ i, a i≠0)
    (hnp : ∀ i j, i≠j → ∀ c : ℝ, ¬∀ k, (a j k : ℝ)=c*(a i k : ℝ))
    (w : I → ℝ) (hw : ∀ i, 0<w i) (hs : 2*∑ i, w i<1) :
    ∃ H : ℕ, 1≤H ∧ ∃ θ : Fin H → J → UnitAddCircle,
      ∀ e f : Bool, ∀ i j : I, ∀ h v : Fin H, (e,i,h)≠(f,j,v) →
        Disjoint (circleInterval (signedCircle e (∑ k, a i k • θ h k)) (w i/H))
          (circleInterval (signedCircle f (∑ k, a j k • θ v k)) (w j/H)) := by sorry
