-- Prove2me | Theorems.Thm_HypercliqueCircuits_Circuits_theorem_6
-- name    : HypercliqueCircuits.Circuits.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T00:36:07.474206+00:00
-- url     : https://prove2.me/theorems/df4ea50f-22ec-48c0-8fd0-cf13483cb973
-- title:
--   Theorem 6 — inductive hyperclique circuit bound
-- statement:
--   Let $k\ge4$, $0<\epsilon\le1/8$, and let $B\ge16$ satisfy $2^{\epsilon B}\ge(eB)^2$. Work over a commutative ring in which $2$ is a unit. If the $(k-1)$-hyperclique polynomials have circuits of size $O(n^{k-1-\epsilon})$ for all positive $n$, then the $k$-hyperclique polynomials have circuits of size
--
--   $$O\bigl(n^{k-\epsilon/(4B)}\bigr)$$
--
--   for all positive $n$. Each size bound has a constant before all dimensions. The premise contains no uniformity condition and permits arbitrary literal constants of the same coefficient ring. All dimensions are covered, rather than only powers of $2^B$. This is the source's size-only inductive step.
--
--   Differences from the source:
--   - generalization: the source dyadic coefficient setting and its size-only induction → arbitrary literal coefficients over any commutative ring in which 2 is a unit; reason: the construction only needs the inverse of 2; taking the dyadic ring gives the source instance without a uniformity premise
--   - reading: arithmetic circuit size without a leaf-count convention → total vertices, including all declared variable sources and literal constant sources; output pointers are free; reason: fixes one size convention for every result; sharing and exact factors are audited in MODERATION_NOTES.md
--   - encoding: one-based coordinate tuples and deletion of position j → Fin coordinates and functions on the ordered subtype of positions other than j; reason: the increasing-coordinate bijection preserves all variables and every monomial
--   - encoding: O bounds with fixed parameters and changing dimensions → positive constants quantified before every changing dimension and subset, with all positive sizes covered; reason: finite small sizes can be absorbed in a constant depending only on the displayed fixed parameters
-- source:
--   Josh Alman, Baitian Li, Neha Pant, Kevin Pratt, Ryan Williams, Finding Hypercliques Faster Than Brute Force, STOC 2027 submission #1224 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1224.pdf, Theorem 6, p.17 (PDF 18), proof p.23 (PDF 24).

import Definitions.Def_HypercliqueCircuits_Circuits_Transpose
import Definitions.Def_HypercliqueCircuits_Circuits_Machine

set_option autoImplicit false

namespace HypercliqueCircuits.Circuits

/-- Theorem 6, printed p.17 / PDF 18; all positive n, with no uniformity premise. -/
theorem theorem_6 (R : Type) [CommRing R] (h2 : IsUnit (2 : R)) (k : ℕ) (hk : 4 ≤ k) (ε : ℝ) (B : ℕ)
    (hB : Admissible ε B) (hind : HasSizeBoundOver R (k-1) ((k-1 : ℕ)-ε)) :
    HasSizeBoundOver R k ((k : ℝ)-ε/(4*B)) := by sorry

end HypercliqueCircuits.Circuits
