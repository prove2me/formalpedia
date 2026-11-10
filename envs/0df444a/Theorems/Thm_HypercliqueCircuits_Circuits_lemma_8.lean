-- Prove2me | Theorems.Thm_HypercliqueCircuits_Circuits_lemma_8
-- name    : HypercliqueCircuits.Circuits.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T00:35:46.256194+00:00
-- url     : https://prove2.me/theorems/69e697de-e24a-4688-b00d-871049cc4749
-- title:
--   Lemma 8 — low-degree circuit bound
-- statement:
--   Fix $k=r+3\ge4$, $0<\epsilon\le1/8$ and an integer $B\ge16$ satisfying $2^{\epsilon B}\ge(eB)^2$. Assume the $(k-1)$-hyperclique family has a size-only bound $O(n^{k-1-\epsilon})$. Put $q=2^B$, $n=q^d$ and $t=\lfloor d/B\rfloor$ for every $d\ge0$.
--
--   Over any commutative ring in which $2$ is a unit, the computed low-degree operator $L$ gives a circuit with
--
--   $$|C_d|\le C n^{k-\epsilon/(4B)}.$$
--
--   One $C$ works for every $d$, with permitted dependence on the fixed induction data. Both contractions are computed from the original variables inside the circuit. The theorem assumes neither their values as inputs nor a decomposition, edge bound or contraction-size certificate.
--
--   Differences from the source:
--   - generalization: the source dyadic coefficient setting and its size-only induction → arbitrary literal coefficients over any commutative ring in which 2 is a unit; reason: the construction only needs the inverse of 2; taking the dyadic ring gives the source instance without a uniformity premise
--   - reading: arithmetic circuit size without a leaf-count convention → total vertices, including all declared variable sources and literal constant sources; output pointers are free; reason: fixes one size convention for every result; sharing and exact factors are audited in MODERATION_NOTES.md
--   - encoding: k at least 4, n=q^d, t=floor(d/B) → k=r+3 with r at least 1, rows indexed directly by q-ary digit vectors; reason: this parametrizes exactly the source dimensions, including d=0
--   - encoding: O bounds with fixed parameters and changing dimensions → positive constants quantified before every changing dimension and subset, with all positive sizes covered; reason: finite small sizes can be absorbed in a constant depending only on the displayed fixed parameters
-- source:
--   Josh Alman, Baitian Li, Neha Pant, Kevin Pratt, Ryan Williams, Finding Hypercliques Faster Than Brute Force, STOC 2027 submission #1224 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1224.pdf, Lemma 8, p.21 (PDF 22), proof pp.21–23 (PDF 22–24).

import Definitions.Def_HypercliqueCircuits_Circuits_Transpose
import Definitions.Def_HypercliqueCircuits_Circuits_Machine

set_option autoImplicit false

namespace HypercliqueCircuits.Circuits

/-- Lemma 8, printed p.21 / PDF 22; neither contraction is a free circuit input. -/
theorem lemma_8 (R : Type) [CommRing R] (h2 : IsUnit (2 : R)) (r : ℕ) (hr : 1 ≤ r) (ε : ℝ) (B : ℕ)
    (hB : Admissible ε B) (hind : HasSizeBoundOver R (r+2) ((r+2 : ℕ)-ε)) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ,
      ∃ c : Circuit R (SplitVar r (Digits (2^B) d)) 1,
        c.polynomial id 0 =
          twist R r (Digits (2^B) d) (lowOperator (2^B) d (d/B)) ∧
        (c.size : ℝ) ≤ C * (((2^B)^d : ℕ) : ℝ) ^ ((r+3 : ℕ)-ε/(4*B)) := by sorry

end HypercliqueCircuits.Circuits
