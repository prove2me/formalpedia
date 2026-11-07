-- Prove2me | Theorems.Thm_MonDepMW_theorem_4_1
-- name    : MonDepMW.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:51:53.606811+00:00
-- url     : https://prove2.me/theorems/cba78662-4be0-4916-9b20-6e6fcd1e4551
-- title:
--   Theorem 4.1 — Damping Theorem
-- statement:
--   Let $r\geqslant1$ and let $\mathcal C$ be a monadically dependent graph class. There is a function $h$ with $h(n)\leqslant\mathrm{subpoly}_{\mathcal C,r}(n)$ such that for any $q\geqslant1$, $n$-vertex $G\in\mathcal C$ and $A\subseteq V(G)$ there are a set $S\subseteq V(G)$ and an $S$-flip $H$ of $G$ with:
--
--   1. $|S|\leqslant|A|/q$;
--   2. for every vertex $u$, $\mathrm{Ball}^r_H[u]$ intersects at most $q^r\cdot h(n)$ parts of $\mathcal T_1(G,A\cup S)$.
--
--   Also, there is an algorithm that, given $q,r,G,A$, computes such $S$ and $H$ in time $\widehat{\mathcal O}_{\mathcal C,r}(n^3)$.
--
--   This is the key technical ingredient: $S$ and $H$ act as a damper for $A$, while $S$ is only a fixed fraction of $A$.
--
--   **Formalization Note** $A$ may be empty. Input: $n$, adjacency matrix, $q$, $r$, the bits of $A$. Output: the bits of $S$, then the adjacency matrix of $H$.
--
--   Differences from the source:
--   - encoding: a graph class → GraphClass, members on each Fin n, no isomorphism closure; reason: every finite graph has a copy on some Fin n, and all quantities are isomorphism invariant
--   - encoding: Ô_{C,r}(n³) → (n+1)³·g(n) with g subpolynomial, chosen with the program before the instance; reason: Ô hides subpolynomial factors (p.11); n+1 only matters at n = 0, where n³·g(n) = 0 would forbid halting
--   - encoding: an algorithm on the RAM model with words of length O(log n) (App. C, p.43) → one program of the published word RAM, correct at every word size above b·(⌊log₂(n + inputs + 2)⌋+1), input in fixed cells, output read by a decoder of the output cells and n; reason: the paper names the model only; the layout is fixed once for all items and the decoders never see the input object
--   - encoding: h : N → N with h(n) ⩽ subpoly(n) → h : ℕ → ℕ with Subpolynomial h; reason: a function bounded by a subpolynomial function is itself subpolynomial (squeeze), and conversely; N is the positive integers; the value at 0 is not constrained by the limit and enters only on the empty graph, where every bound holds, or not at all
-- source:
--   Dreier, Mählmann, Pilipczuk, Toruńczyk, Monadically Dependent Graph Classes Have Almost Bounded Merge-Width, arXiv:2611.06804 (held version, sha256 6e4b0608…), Theorem 4.1, p.15 (restated p.34)

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_WordRAM
import Definitions.Def_MonDepMW_RunsWithin
import Definitions.Def_MonDepMW_decodeSet
import Definitions.Def_MonDepMW_Subpolynomial
import Definitions.Def_MonDepMW_MonadicallyDependent
import Definitions.Def_MonDepMW_IsDamper

set_option autoImplicit false

open TrulySubcubicAPSP

namespace MonDepMW

/-- **Theorem 4.1 (Damping Theorem).** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), p.15, restated p.34: "Let r ∈ N and C be a monadically dependent graph class.
Then there exists a function h : N → N with h(n) ⩽ subpoly_{C,r}(n) such that for any q ∈ N, n-vertex graph G ∈ C, and
vertex subset A ⊆ V (G), there exist a set S ⊆ V (G) and an S-flip H of G satisfying the following properties: |S| ⩽ |A|/q;
and for every vertex u ∈ V (G), Ball^r_H[u] intersects at most q^r · h(n) parts of 𝒯1(G, A ∪ S). Also, there is an
algorithm that, given q, r, G, and A, computes such a set S and an S-flip H in time Ô_{C,r}(n³)."

**Formalization Note.** `A` may be empty. `Ô_{C,r}(n³)` is `(n + 1)³ · g(n)` with `g` subpolynomial, chosen before `q`, `G`,
`A`. Input: `n`, adjacency matrix, `q`, `r`, the `n` cells of `A`. Output: the `n` cells of `S`, then the `n²` cells of `H`. -/
theorem theorem_4_1 (r : ℕ) (hr : 1 ≤ r) (𝒞 : GraphClass) (h𝒞 : MonadicallyDependent 𝒞) :
    ∃ h : ℕ → ℕ, Subpolynomial h ∧
      (∀ q : ℕ, 1 ≤ q → ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G ∈ 𝒞 n → ∀ A : Finset (Fin n),
        ∃ (S : Finset (Fin n)) (H : SimpleGraph (Fin n)), IsDamper G A S H q r (q ^ r * h n)) ∧
      ∃ (P : List Instr) (b : ℕ) (g : ℕ → ℕ), Subpolynomial g ∧
        ∀ q : ℕ, 1 ≤ q → ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G ∈ 𝒞 n → ∀ (A : Finset (Fin n)) (W : ℕ),
          b * (Nat.log2 (n + q + r + 2) + 1) ≤ W →
          RunsWithin P W ((n + 1) ^ 3 * g n) (graphInput G ++ [(q : ℤ), (r : ℤ)] ++ setBits A) fun out =>
            IsDamper G A (decodeSet n out 0) (decodeGraph n out n) q r (q ^ r * h n) := by sorry

end MonDepMW
