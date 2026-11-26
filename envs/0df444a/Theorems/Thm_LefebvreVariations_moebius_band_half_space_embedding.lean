-- Prove2me | Theorems.Thm_LefebvreVariations_moebius_band_half_space_embedding
-- name    : LefebvreVariations.moebius_band_half_space_embedding
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:07:52.811214+00:00
-- url     : https://prove2.me/theorems/debabf02-1d55-4986-9653-0cc95b77a74d
-- title:
--   Lefebvre's variations, No. 146 — on a theme by Vaughan: the Möbius band does not embed in a half-space with boundary exactly on the bounding plane
-- statement:
--   *Lefebvre's variations — posed by Erwan Lefebvre.*
--
--   Let $M = \mathrm{Sym}^2(S^1)$ be the space of unordered pairs of points of the circle $S^1 = \mathbb{R}/\mathbb{Z}$; it is a Möbius band whose boundary circle is the diagonal $\{\{s,s\}\}$. Write a point of $M$ as the class of a pair $(s,t) \in \mathbb{R}^2$ modulo $(s,t) \sim (t,s)$, $(s,t) \sim (s+1,t)$. Let $\Phi : M \to \mathbb{R}^2 \times \mathbb{R}$ be continuous, with third coordinate $\Phi_3 \ge 0$, such that $\Phi_3(s,t) = 0$ exactly when $s \equiv t \pmod 1$ (that is, exactly on the boundary of $M$), and such that the restriction of $\Phi$ to the boundary is injective (the planar part $\Phi_{12}(s,s)$ takes distinct values at distinct points of the circle). Then $\Phi$ is **not injective**: there are two distinct points of $M$ with the same image.
--
--   In other words, the Möbius band has no topological embedding into the closed half-space $\mathbb{R}^2 \times [0,\infty)$ meeting the plane $\mathbb{R}^2 \times \{0\}$ exactly in its boundary circle. Proof sketch: such an embedding and its mirror image $(x,y,z) \mapsto (x,y,-z)$ glue along the boundary into an embedding of the Klein bottle $M \cup_{\partial M} M$ in $\mathbb{R}^3$, which does not exist (the Klein bottle is a closed non-orientable surface, and a closed surface embedded in $\mathbb{R}^3$ separates it and is orientable; see Samelson, Proc. AMS 22 (1969)).
--
--   **Formalization Note** The Möbius band is not built as a space: a map on it is a continuous $\Phi : \mathbb{R} \times \mathbb{R} \to \mathbb{R}^2 \times \mathbb{R}$ (`EuclideanSpace ℝ (Fin 2) × ℝ`) invariant under the swap and under $s \mapsto s+1$ (invariance in $t$ follows), so it is exactly a map on $\mathrm{Sym}^2(\mathbb{R}/\mathbb{Z})$. The hypotheses are `hswap`, `hper`, `hnonneg` ($\Phi_3 \ge 0$), `hzero` ($\Phi_3(s,t) = 0$ iff $t - s \in \mathbb{Z}$) and `hbdry` (equal planar parts at $(s,s)$ and $(t,t)$ force $t - s \in \mathbb{Z}$). The conclusion gives $(s,t), (s',t')$ with $\Phi(s,t) = \Phi(s',t')$ whose classes differ, i.e. $(s',t')$ is neither $(s,t)$ nor $(t,s)$ modulo $\mathbb{Z}^2$. The statement is for a continuous (not smooth) $\Phi$, as the Jordan curve application needs.
--
--   **Why this is a Lefebvre variation.** It is the missing step of a Lean-verified reduction of the open statement `SquarePeg.vaughan_inscribed_rectangle` (every Jordan curve inscribes a rectangle, Vaughan). Parametrize the curve by $\gamma$, set $\Phi(s,t) = \big(\tfrac12(\gamma(s)+\gamma(t)),\, |\gamma(t)-\gamma(s)|\big)$ (midpoint and length of the chord), check the hypotheses (the boundary is the set of degenerate chords, injective because $\gamma$ is), and read two distinct chords with the same midpoint and length as the diagonals of a rectangle. It is not a special case of the base statement: it is a general topological fact about the Möbius band (the non-embeddability of the Klein bottle in $\mathbb{R}^3$, in a half-space form) that is the one missing ingredient of the verified reduction.
--
--   **Attribution.** Series *Lefebvre's variations*, posed by Erwan Lefebvre.
-- source:
--   Posed by Erwan Lefebvre (series Lefebvre's variations). Vaughan's argument (H. E. Vaughan, in D. Meyerson, Balancing acts, Topology Proceedings 6 (1981), 59–66; exposition: I. Pak, Lectures on Discrete and Polyhedral Geometry, ch. on the square peg problem; B. Matschke, A survey on the square peg problem, Notices AMS 61 (2014), 346–352): the map {p,q} -> (midpoint, |p-q|) from the Möbius band of unordered pairs of the curve to R^3 would otherwise embed it with boundary on the plane z=0 and interior in z>0, and doubling gives a Klein bottle embedded in R^3. Non-embeddability of the Klein bottle in R^3: H. Samelson, Orientability of hypersurfaces in R^n, Proc. AMS 22 (1969), 301–302 (also Hatcher, Algebraic Topology, via Alexander duality / Z/2-homology). Citations written from memory (no network). Origin of this statement: it is the missing step of a reduction of SquarePeg.vaughan_inscribed_rectangle (every Jordan curve inscribes a rectangle). The Lean-verified reduction parametrizes the Jordan curve periodically, applies the statement to Phi(s,t) = (midpoint, chord length), checks the hypotheses (boundary = degenerate chords, injective since the parametrization is injective mod 1), and turns two distinct unordered pairs with equal midpoint and length into the four vertices of a nondegenerate rectangle. Everything except the statement is proved in Lean.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations
theorem moebius_band_half_space_embedding
    (Φ : ℝ × ℝ → EuclideanSpace ℝ (Fin 2) × ℝ) (hΦ : Continuous Φ)
    (hswap : ∀ s t : ℝ, Φ (s, t) = Φ (t, s))
    (hper : ∀ s t : ℝ, Φ (s + 1, t) = Φ (s, t))
    (hnonneg : ∀ s t : ℝ, 0 ≤ (Φ (s, t)).2)
    (hzero : ∀ s t : ℝ, (Φ (s, t)).2 = 0 ↔ ∃ n : ℤ, t = s + n)
    (hbdry : ∀ s t : ℝ, (Φ (s, s)).1 = (Φ (t, t)).1 → ∃ n : ℤ, t = s + n) :
    ∃ s t s' t' : ℝ, Φ (s, t) = Φ (s', t') ∧
      ¬ ((∃ m n : ℤ, s' = s + m ∧ t' = t + n) ∨ (∃ m n : ℤ, s' = t + m ∧ t' = s + n)) := by sorry
end LefebvreVariations
