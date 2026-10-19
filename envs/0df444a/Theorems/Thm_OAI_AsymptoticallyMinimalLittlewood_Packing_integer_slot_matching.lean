-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_integer_slot_matching
-- name    : OAI.AsymptoticallyMinimalLittlewood.Packing.integer_slot_matching
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:45:46.644602+00:00
-- url     : https://prove2.me/theorems/8b27de30-dec3-4005-84b6-aef8634e5740
-- title:
--   Many points whose integer-linear images all land in distinct signed slots modulo a prime
-- statement:
--   Let $r\ge2$ and $m\ge0$ be integers and let $a=(a_{ik})\in\mathbb{Z}^{r\times m}$ be an integer matrix with rows $a_0,\dots,a_{r-1}$. Assume that every row is nonzero and that no row is a rational multiple of another: $a_l\neq c\,a_j$ for all $j\neq l$ and all $c\in\mathbb{Q}$. Let $d=(d_0,\dots,d_{r-1})\in\mathbb{N}^r$, put $L_i=2d_i+1$, $L=\sum_iL_i$, $P_i=\sum_{j<i}L_j$, and let $t$ be a real number with
--   $$0<t<\frac{1}{2L}.$$
--
--   For integers $R,K$ and a prime $q$, a *slot choice* is a family $\omega=(\sigma_k,\epsilon_k)_{0\le k<K}$ of shifts $\sigma_k\in\{0,\dots,L-1\}$ and signs $\epsilon_k\in\{+1,-1\}$, and row $i$ is *hit* at $u\in\mathbb{Z}/q\mathbb{Z}$ under $\omega$ if
--   $$u\equiv\epsilon_k\big(kRL+pL+\sigma_k+P_i+d_i+1\big)\pmod q\quad\text{for some }0\le k<K,\ 0\le p<R-1,$$
--   that is, $\pm u$ is the centre of the $i$-th slot (a block of $L_i$ consecutive integers) in some period $p$ of some chunk $k$. For $y\in(\mathbb{Z}/q\mathbb{Z})^m$ write $\langle a_i,y\rangle=\sum_k a_{ik}y_k\in\mathbb{Z}/q\mathbb{Z}$.
--
--   Then there exist a prime $q$, integers $R\ge3$ and $K\ge1$ with $2KRL<q$, a slot choice $\omega$ and a finite set $M\subseteq(\mathbb{Z}/q\mathbb{Z})^m$ such that
--   1. for every $y\in M$ and every row $i$, row $i$ is hit at $\langle a_i,y\rangle$ under $\omega$;
--   2. for all distinct $y,z\in M$ and every row $i$, $\langle a_i,y\rangle\neq\langle a_i,z\rangle$;
--   3. $|M|>t\,q$.
--
--   Each point of $M$ thus places all $r$ values $\langle a_i,y\rangle$ at slot centres, and different points never share a slot of the same row. Since each row has at most $K(R-1)<q/(2L)$ hit residues, property 2 forces $|M|<q/(2L)$; the theorem shows that every density $t$ below this trivial bound is attained. Reduced to the circle, the points of $M$ give the phase vectors of the signed interval packing used in the construction of flat Littlewood polynomials.
--
--   **Formalization Note** Slot choices are `SlotChoices d K`, maps `Fin K → Fin L × Bool` with `true` meaning the sign $+1$; the hit relation is `slotHit d R K q`, and $\langle a_i,y\rangle$ is `dotProduct` of the reduced row with $y$. The hypotheses on the rows are stated for the rows viewed as vectors of rationals.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/IntervalPacking.lean#L50-L136

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
open Finset Nibble Filter Topology
attribute [local instance] Classical.propDecidable

theorem OAI.AsymptoticallyMinimalLittlewood.Packing.integer_slot_matching {r m : ℕ} (hr : 2≤r)
    (a : Fin r → Fin m → ℤ)
    (ha : ∀ j, (fun k ↦ (a j k : ℚ))≠0)
    (hnp : ∀ j l, j≠l → ∀ c : ℚ,
      (fun k ↦ (a l k : ℚ))≠c • (fun k ↦ (a j k : ℚ)))
    (d : Fin r → ℕ) {t : ℝ} (ht0 : 0<t) (ht : t<1/(2*periodLength (oddLengths d) : ℝ)) :
    ∃ q R K : ℕ, q.Prime ∧ 3≤R ∧ 0<K ∧ 2*(K*(R*periodLength (oddLengths d)))<q ∧
      ∃ ω : SlotChoices d K, ∃ M : Finset (Fin m → ZMod q),
        (∀ y∈M, ∀ i, slotHit d R K q i ω (dotProduct (fun k ↦ (a i k : ZMod q)) y)) ∧
        (∀ y∈M, ∀ z∈M, y≠z → ∀ i,
          dotProduct (fun k ↦ (a i k : ZMod q)) y≠dotProduct (fun k ↦ (a i k : ZMod q)) z) ∧
        t*q<(M.card : ℝ) := by sorry
