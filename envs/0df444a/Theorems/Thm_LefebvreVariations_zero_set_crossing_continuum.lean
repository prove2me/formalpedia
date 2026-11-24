-- Prove2me | Theorems.Thm_LefebvreVariations_zero_set_crossing_continuum
-- name    : LefebvreVariations.zero_set_crossing_continuum
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T22:40:48.318957+00:00
-- url     : https://prove2.me/theorems/ad4b9417-d21a-410b-8639-59cc182becc4
-- title:
--   Lefebvre's variations: the zero set of a function changing sign across a rectangle contains a continuum crossing it
-- statement:
--   Let $a \le b$ and $c \le d$ be real numbers, let $R = [a,b] \times [c,d]$, and let $F : R \to \mathbb{R}$ be continuous with
--
--   $$
--   F(a,t) \ge 0 \quad\text{and}\quad F(b,t) \le 0 \qquad \text{for every } t \in [c,d],
--   $$
--
--   that is, $F$ is nonnegative on the left side of the rectangle and nonpositive on its right side. Then the zero set $F^{-1}(0)$ contains a connected set $W$ that meets both the bottom side $[a,b] \times \{c\}$ and the top side $[a,b] \times \{d\}$.
--
--   This is the classical crossing (or "zero-set continuum") lemma of planar topology. It is the continuous form of the Hex / Steinhaus chessboard theorem: for a closed set $K \subseteq R$, either $K$ contains a connected set joining the bottom and top sides, or $R \setminus K$ contains a connected set joining the left and right sides. Applied to $K = F^{-1}(0)$, the second alternative is impossible by the intermediate value theorem, which gives the statement. It implies the two-dimensional Poincaré–Miranda theorem (if moreover $G \ge 0$ on the bottom side and $G \le 0$ on the top side, then $G$ vanishes on $W$), hence the two-dimensional Brouwer fixed point theorem.
--
--   **Formalization Note** The rectangle is `Set.Icc a b ×ˢ Set.Icc c d` in `ℝ × ℝ` with its product topology. `F` is a function `ℝ × ℝ → ℝ`, required to be continuous only on the rectangle (`ContinuousOn`); its values outside the rectangle play no role. The connected set is a `W : Set (ℝ × ℝ)` with `IsPreconnected W` (it is nonempty, since it meets the bottom side), contained in the rectangle, on which `F` vanishes; meeting the bottom (top) side is written `∃ s, (s, c) ∈ W` (`∃ s, (s, d) ∈ W`), and `s ∈ [a,b]` follows from `W` lying in the rectangle. The hypotheses `a ≤ b` and `c ≤ d` only exclude an empty rectangle; the degenerate cases `a = b` or `c = d` are included and true.
-- source:
--   Classical planar topology. Continuous form of the Hex theorem: D. Gale, The game of Hex and the Brouwer fixed-point theorem, Amer. Math. Monthly 86 (1979), 818–827 (Hex theorem, equivalence with the Brouwer fixed point theorem in the plane); Steinhaus' chessboard theorem and its use for the Poincaré–Miranda theorem: W. Kulpa, The Poincaré–Miranda theorem, Amer. Math. Monthly 104 (1997), 545–550, and P. Tkacz, M. Turzański, An n-dimensional version of Steinhaus' chessboard theorem, Topology Appl. 155 (2008); crossing of paths joining opposite sides of a square from Brouwer's theorem: R. Maehara, The Jordan curve theorem via the Brouwer fixed point theorem, Amer. Math. Monthly 91 (1984), 641–643; separation in the square (unicoherence): K. Kuratowski, Topology, vol. II (1968), §61. Origin of this statement: it is the missing step of a reduction of SquarePeg.nielsen_wright_symmetric_curve (Nielsen–Wright, Rectangles inscribed in symmetric continua, Geom. Dedicata 56 (1995): every Jordan curve symmetric across a line or about a point inscribes a square). The verified reduction parametrizes the curve periodically and treats both symmetries with the lemma. Line symmetry (axis a + ℝu): it finds an excursion of the curve off the axis (parameters u0 < v0 with both ends on the axis, strictly on one side in between), applies the lemma on [u0, t*] × [t*, v0] (t* the first time of greatest distance to the axis) to F(s,t) = X(t) − X(s) (X the signed distance to the axis), and an intermediate value argument on the connected zero set gives two points at the same distance x ≠ 0 from the axis and 2x apart along it; with their mirror images they form a square. Point symmetry (centre z): it proves z is not on the curve (a closed-set and connectedness argument on the parameter interval), takes the last parameter at minimal distance to z and the next one at maximal distance, applies the lemma to F(s,t) = |γ(t) − z| − |γ(s) − z| on a rectangle whose top side ends at the antipode of the farthest point, and the intermediate value theorem for ⟨γ(s) − z, γ(t) − z⟩ on the connected zero set gives two points at the same distance from z in perpendicular directions, i.e. a square centred at z. Everything except the lemma is proved in Lean.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations
theorem zero_set_crossing_continuum (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (F : ℝ × ℝ → ℝ) (hF : ContinuousOn F (Set.Icc a b ×ˢ Set.Icc c d))
    (hleft : ∀ t ∈ Set.Icc c d, 0 ≤ F (a, t))
    (hright : ∀ t ∈ Set.Icc c d, F (b, t) ≤ 0) :
    ∃ W : Set (ℝ × ℝ), W ⊆ Set.Icc a b ×ˢ Set.Icc c d ∧ (∀ p ∈ W, F p = 0) ∧
      IsPreconnected W ∧ (∃ s : ℝ, (s, c) ∈ W) ∧ (∃ s : ℝ, (s, d) ∈ W) := by sorry
end LefebvreVariations
