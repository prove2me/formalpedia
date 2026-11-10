-- Prove2me | Theorems.Thm_HypercliqueCircuits_Circuits_corollary_1
-- name    : HypercliqueCircuits.Circuits.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T00:35:48.919783+00:00
-- url     : https://prove2.me/theorems/58b7f4db-1540-47af-9066-b86e202d3881
-- title:
--   Corollary 1 — high-degree circuit bound
-- statement:
--   Fix $k=r+3\ge4$, $0<\epsilon\le1/8$ and an integer $B\ge16$ satisfying $2^{\epsilon B}\ge(eB)^2$. Assume the $(k-1)$-hyperclique family has a size-only bound $O(n^{k-1-\epsilon})$. Put $q=2^B$, $n=q^d$ and $t=\lfloor d/B\rfloor$ for every $d\ge0$.
--
--   The computed high-degree operator $H$ gives a circuit for its twisted polynomial with
--
--   $$|C_d|\le C n^{k-\epsilon/(2B)}.$$
--
--   The constant is independent of $d$. The premise is only a circuit-size bound for the lower-dimensional family; it supplies no free contraction or uniform algorithm. This is the high-degree contribution to the inductive theorem.
--
--   Differences from the source:
--   - generalization: arithmetic circuits in the source coefficient setting → circuits with arbitrary literal coefficients over every commutative ring; reason: the division-free identities apply over these rings and specialize to the dyadic source setting
--   - reading: arithmetic circuit size without a leaf-count convention → total vertices, including all declared variable sources and literal constant sources; output pointers are free; reason: fixes one size convention for every result; sharing and exact factors are audited in MODERATION_NOTES.md
--   - encoding: k at least 4, n=q^d, t=floor(d/B) → k=r+3 with r at least 1, rows indexed directly by q-ary digit vectors; reason: this parametrizes exactly the source dimensions, including d=0
--   - encoding: O bounds with fixed parameters and changing dimensions → positive constants quantified before every changing dimension and subset, with all positive sizes covered; reason: finite small sizes can be absorbed in a constant depending only on the displayed fixed parameters
-- source:
--   Josh Alman, Baitian Li, Neha Pant, Kevin Pratt, Ryan Williams, Finding Hypercliques Faster Than Brute Force, STOC 2027 submission #1224 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1224.pdf, Corollary 1, p.19 (PDF 20).

import Definitions.Def_HypercliqueCircuits_Circuits_Transpose
import Definitions.Def_HypercliqueCircuits_Circuits_Machine

set_option autoImplicit false

namespace HypercliqueCircuits.Circuits

/-- Corollary 1, printed p.19 / PDF 20. -/
theorem corollary_1 (R : Type) [CommRing R] (r : ℕ) (hr : 1 ≤ r) (ε : ℝ) (B : ℕ)
    (hB : Admissible ε B) (hind : HasSizeBoundOver R (r+2) ((r+2 : ℕ)-ε)) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ,
      ∃ c : Circuit R (SplitVar r (Digits (2^B) d)) 1,
        c.polynomial id 0 =
          twist R r (Digits (2^B) d) (highOperator (2^B) d (d/B)) ∧
        (c.size : ℝ) ≤ C * (((2^B)^d : ℕ) : ℝ) ^ ((r+3 : ℕ)-ε/(2*B)) := by sorry

end HypercliqueCircuits.Circuits
