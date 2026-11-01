-- Prove2me | Theorems.Thm_MaxEntCont_theorem_5_6_two_of_one
-- name    : MaxEntCont.theorem_5_6_two_of_one
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:18:45.606519+00:00
-- url     : https://prove2.me/theorems/f2349127-e937-4648-b061-753bc3e7f8f1
-- title:
--   Proof of Theorem 5.6 — statement (2) follows from statement (1) for any convex body $L$
-- statement:
--   Let $L$ be a convex body (compact convex set) in a finite-dimensional real normed space $Y$, and let $F(u)$ denote the face of $L$ containing $u$ in its relative interior. Let $(w_i)_{i\in\mathbb N}\subseteq L$ converge to $w\in L$, and suppose that
--
--   (1) for every open set $O$ meeting $F(w)$ there is $N\in\mathbb N$ such that $O\cap F(w_i)\neq\emptyset$ for all $i\ge N$.
--
--   Then
--
--   (2)
--   $$
--   \dim F(w)\le\liminf_{i\to\infty}\dim F(w_i).
--   $$
--
--   The paper records this step of the proof of Theorem 5.6 as "an easy corollary of (1) for arbitrary convex bodies $L$": lower semicontinuity of the faces along the sequence forces lower semicontinuity of their dimensions.
--
--   **Formalization Note** $F(\cdot)$ is `minFace L ·` and $\dim F(\cdot)$ is `MaxEntCont.faceDim L ·`. The lim inf is taken in $\mathbb N\cup\{\infty\}$ (`ℕ∞`), a complete lattice, so it needs no boundedness side condition. "There is $N$ such that for all $i\ge N$" is `∀ᶠ i in atTop`.
--
--   Differences from the source:
--   - encoding: open subsets $O\subseteq L$ meeting $F(w)$ → open subsets $O$ of $Y$, intersected with $F(\cdot)$; reason: $F(\cdot)\subseteq L$, so $(O\cap L)\cap F(\cdot)=O\cap F(\cdot)$
--   - encoding: $\liminf$ of natural numbers → `Filter.liminf` in `ℕ∞` of the cast values; reason: the same value, without Lean's junk value for an unbounded liminf in ℕ
--   - encoding: $F(\cdot)$, $\dim$ → `minFace`, `finrank ℝ (vectorSpan ℝ ·)`; reason: Fact 5.3 and the dimension of the affine hull
--   - encoding: "there exists $N$ such that for all $i\ge N$" → `∀ᶠ i in atTop`; reason: the same statement
--   - encoding: all sets lie in a finite-dimensional real normed space (standing assumption, p. 4) → explicit `[FiniteDimensional ℝ Y]` binder; reason: the paper's tacit assumption, made explicit
-- source:
--   Rodman, Spitkovsky, Szkoła, Weis, Continuity of the maximum-entropy inference, arXiv:1502.02018v1, proof of Theorem 5.6, p. 14

import Mathlib
import Definitions.Def_TriangleFace
import Definitions.Def_MaxEntCont_faceDim

namespace MaxEntCont

open OAI.CanonicalFace198 Filter Topology

/-- **Theorem 5.6: (2) follows from (1)** (Rodman, Spitkovsky, Szkoła, Weis, *Continuity of the maximum-entropy inference*, arXiv:1502.02018v1, proof of Theorem 5.6, p. 14): "The statement (2)
is an easy corollary of (1) for arbitrary convex bodies `L`."

Let `L` be a convex body (compact convex set) in `Y` and let `(wᵢ) ⊂ L` converge to `w ∈ L`. If
every open set meeting `F(w)` meets `F(wᵢ)` for all sufficiently large `i` (statement (1) of
Theorem 5.6), then `dim F(w) ≤ lim inf_{i→∞} dim F(wᵢ)` (statement (2)).

**Formalization Note** `F(·) = minFace L ·` (`MaxEntCont.fact_5_3`) and `dim F(·)` is
`MaxEntCont.faceDim L ·`. Open subsets of `L` are traces `O ∩ L` of open `O ⊆ Y`; since
`F(·) ⊆ L`, `(O ∩ L) ∩ F(·) = O ∩ F(·)`. "There exists `N` with … for all `i ≥ N`" is
`∀ᶠ i in atTop`. The lim inf is taken in `ℕ∞` (a complete lattice, so no boundedness side
conditions). The paper states this inside the setting of Theorem 5.6, where `wᵢ → w`; the
convergence hypothesis is kept. -/
theorem theorem_5_6_two_of_one {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ Y] (L : Set Y) (hLc : IsCompact L) (hLv : Convex ℝ L)
    (w : Y) (hw : w ∈ L) (ws : ℕ → Y) (hws : ∀ i, ws i ∈ L) (hlim : Tendsto ws atTop (𝓝 w))
    (h1 : ∀ O : Set Y, IsOpen O → (O ∩ minFace L w).Nonempty →
      ∀ᶠ i in atTop, (O ∩ minFace L (ws i)).Nonempty) :
    (faceDim L w : ℕ∞) ≤ Filter.liminf (fun i => (faceDim L (ws i) : ℕ∞)) atTop := by sorry

end MaxEntCont
