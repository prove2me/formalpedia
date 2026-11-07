-- Prove2me | Theorems.Thm_MonDepMW_theorem_8_3
-- name    : MonDepMW.theorem_8_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:52:29.590835+00:00
-- url     : https://prove2.me/theorems/338b6a6b-3e27-48bb-ae40-01d2f3c259a0
-- title:
--   Theorem 8.3 — Damping Theorem with explicit bounds
-- statement:
--   Let $r\geqslant1$, let $G$ be a graph, and let $\alpha,\beta,\gamma\geqslant1$ be such that $\mathcal T_{r+1}$ has growth ratio at most $\gamma$ on $G$, $G$ has packing ratio at most $\beta$, and $G$ admits a vertex ordering $\preccurlyeq$ of alternation at most $\alpha$. Then for every $q\geqslant1$ and non-empty $A\subseteq V(G)$ there are $S\subseteq V(G)$ and an $S$-flip $H$ of $G$ with:
--
--   1. $|S|\leqslant|A|/q$;
--   2. for every vertex $u$, $\mathrm{Ball}^r_H[u]$ intersects at most $(265q(\alpha+\beta)\gamma)^r$ parts of $\mathcal T_1(G,A\cup S)$.
--
--   Moreover, there is an algorithm computing such $S$ and $H$, given $r,q,G,A,\preccurlyeq$, in time $\mathcal O((\beta+\gamma)(\beta\gamma+r)|A|n^2)$.
--
--   This form makes the dependence on the three parameters explicit, and implies Theorem 4.1.
--
--   **Formalization Note** $\alpha,\beta,\gamma$ are not inputs: a single run meets the bounds and the time for every $\alpha,\beta,\gamma\geqslant1$ meeting the hypotheses with this $\preccurlyeq$.
--
--   Differences from the source:
--   - encoding: 𝒪(E) → c·(E+1) with c absolute; reason: 𝒪 hides constant factors (p.11); +1 only matters where E can be 0
--   - encoding: an algorithm on the RAM model with words of length O(log n) (App. C, p.43) → one program of the published word RAM, correct at every word size above b·(⌊log₂(n + inputs + 2)⌋+1), input in fixed cells, output read by a decoder of the output cells and n; reason: the paper names the model only; the layout is fixed once for all items and the decoders never see the input object
-- source:
--   Dreier, Mählmann, Pilipczuk, Toruńczyk, Monadically Dependent Graph Classes Have Almost Bounded Merge-Width, arXiv:2611.06804 (held version, sha256 6e4b0608…), Theorem 8.3, p.33

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_WordRAM
import Definitions.Def_MonDepMW_RunsWithin
import Definitions.Def_MonDepMW_decodeSet
import Definitions.Def_MonDepMW_PartitionSelector
import Definitions.Def_MonDepMW_PackingLE
import Definitions.Def_MonDepMW_AlternationLE
import Definitions.Def_MonDepMW_IsDamper

set_option autoImplicit false

open TrulySubcubicAPSP

namespace MonDepMW

/-- **Theorem 8.3 (Damping Theorem with explicit bounds).** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), p.33: "Let r ∈ N, G be a graph, and α, β, γ ∈ N be such that
𝒯r+1 has growth ratio at most γ on G; G has packing ratio at most β; and G admits a vertex ordering ≼ of alternation at most α.
Then for every q ∈ N and a non-empty vertex subset A ⊆ V (G), there exist a set S ⊆ V (G) and an S-flip H of G satisfying the
following properties: |S| ⩽ |A|/q; and for every vertex u ∈ V (G), Ball^r_H[u] intersects at most (265q · (α + β)γ)^r parts of
𝒯1(G, A ∪ S). Moreover, there is an algorithm computing such a set S and an S-flip H, given r, q, G, A, and ≼, in time
𝒪((β + γ)(βγ + r) · |A|n²)."

**Formalization Note.** `c` is absolute. `α, β, γ` are not inputs: a single run meets the bounds and the time for every
`α, β, γ ≥ 1` meeting the hypotheses with this `≼`. Input: `n`, adjacency matrix, `q`, `r`, the `n` cells of `A`, the `n` vertices
in order. Output: the `n` cells of `S`, then the `n²` cells of `H`. -/
theorem theorem_8_3 :
    (∀ r : ℕ, 1 ≤ r → ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (α β γ : ℕ), 1 ≤ α → 1 ≤ β → 1 ≤ γ →
      (rTypeSelector (r + 1)).GrowthLE G γ → PackingLE G β → (∃ σ, AlternationLE G σ α) →
      ∀ q : ℕ, 1 ≤ q → ∀ A : Finset (Fin n), A.Nonempty →
        ∃ (S : Finset (Fin n)) (H : SimpleGraph (Fin n)),
          IsDamper G A S H q r ((265 * q * ((α + β) * γ)) ^ r)) ∧
    ∃ (P : List Instr) (b c : ℕ), ∀ r : ℕ, 1 ≤ r → ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (q : ℕ), 1 ≤ q →
      ∀ (A : Finset (Fin n)), A.Nonempty → ∀ (σ : Fin n ≃ Fin n) (W : ℕ),
      b * (Nat.log2 (n + q + r + 2) + 1) ≤ W → ∀ α β γ : ℕ, 1 ≤ α → 1 ≤ β → 1 ≤ γ →
      (rTypeSelector (r + 1)).GrowthLE G γ → PackingLE G β → AlternationLE G σ α →
      RunsWithin P W (c * ((β + γ) * (β * γ + r) * A.card * n ^ 2 + 1))
        (graphInput G ++ [(q : ℤ), (r : ℤ)] ++ setBits A ++ orderWords σ) fun out =>
          IsDamper G A (decodeSet n out 0) (decodeGraph n out n) q r ((265 * q * ((α + β) * γ)) ^ r) := by sorry

end MonDepMW
