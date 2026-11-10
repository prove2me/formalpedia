-- Prove2me | Theorems.Thm_HypercliqueCircuits_Circuits_lemma_5
-- name    : HypercliqueCircuits.Circuits.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T00:35:54.280509+00:00
-- url     : https://prove2.me/theorems/c8e9cba4-b12a-49f7-9487-eb00e4bbeffa
-- title:
--   Lemma 5 — partial-transpose circuit saving
-- statement:
--   Fix $k=r+3\ge4$, $0<\epsilon\le1/8$ and an integer $B\ge16$ satisfying $2^{\epsilon B}\ge(eB)^2$. Assume the $(k-1)$-hyperclique family has a size-only bound $O(n^{k-1-\epsilon})$. Put $q=2^B$, $n=q^d$ and $t=\lfloor d/B\rfloor$ for every $d\ge0$.
--
--   For every $A\subseteq[d]$, the actual twisted polynomial has a circuit with
--
--   $$|C_{d,A}|\le C n^k q^{-\epsilon|A|}.$$
--
--   One positive $C$ works for every $d$ and $A$, including $A=\varnothing$. The matrices $P^z,Q^z$ are the computed monomials from the original variable groups. This is the source's uniform-in-subsets size estimate, without a generator premise.
--
--   Differences from the source:
--   - generalization: arithmetic circuits in the source coefficient setting → circuits with arbitrary literal coefficients over every commutative ring; reason: the division-free identities apply over these rings and specialize to the dyadic source setting
--   - reading: arithmetic circuit size without a leaf-count convention → total vertices, including all declared variable sources and literal constant sources; output pointers are free; reason: fixes one size convention for every result; sharing and exact factors are audited in MODERATION_NOTES.md
--   - encoding: k at least 4, n=q^d, t=floor(d/B) → k=r+3 with r at least 1, rows indexed directly by q-ary digit vectors; reason: this parametrizes exactly the source dimensions, including d=0
--   - encoding: O bounds with fixed parameters and changing dimensions → positive constants quantified before every changing dimension and subset, with all positive sizes covered; reason: finite small sizes can be absorbed in a constant depending only on the displayed fixed parameters
-- source:
--   Josh Alman, Baitian Li, Neha Pant, Kevin Pratt, Ryan Williams, Finding Hypercliques Faster Than Brute Force, STOC 2027 submission #1224 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1224.pdf, Lemma 5, p.18 (PDF 19), proof continued p.19 (PDF 20).

import Definitions.Def_HypercliqueCircuits_Circuits_Transpose
import Definitions.Def_HypercliqueCircuits_Circuits_Machine

set_option autoImplicit false

namespace HypercliqueCircuits.Circuits

/-- Lemma 5, printed p.18 / PDF 19; one O constant for all d and A, including A=empty. -/
theorem lemma_5 (R : Type) [CommRing R] (r : ℕ) (hr : 1 ≤ r) (ε : ℝ) (B : ℕ)
    (hB : Admissible ε B) (hind : HasSizeBoundOver R (r+2) ((r+2 : ℕ)-ε)) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, ∀ A : Finset (Fin d),
      ∃ c : Circuit R (SplitVar r (Digits (2^B) d)) 1,
        c.polynomial id 0 = twist R r (Digits (2^B) d) (tau A) ∧
        (c.size : ℝ) ≤ C * ((2^B)^d : ℕ) ^ (r+3 : ℕ) *
          (2^B : ℕ) ^ (-ε * A.card) := by sorry

end HypercliqueCircuits.Circuits
