-- Prove2me | Theorems.Thm_MonDepMW_lemma_6_1
-- name    : MonDepMW.lemma_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:53:01.899044+00:00
-- url     : https://prove2.me/theorems/54b46abe-d131-4dce-821a-06bb8d500c86
-- title:
--   Lemma 6.1 — Predamping Lemma
-- statement:
--   Let $\mathcal P$ be a monotone and respectful partition selector, $G$ a graph, and $\alpha,\beta,\gamma\geqslant1$ such that $\mathcal P$ has growth ratio at most $\gamma$ on $G$, $G$ has packing ratio at most $\beta$, and $G$ admits a vertex ordering $\preccurlyeq$ of alternation at most $\alpha$. Then for every $q\geqslant1$ and $A\subseteq V(G)$ with $|A|\geqslant6(q+1)$ there is a set $S$ with:
--
--   1. (A1) $|S|\leqslant|A|/q$;
--   2. (A2) for every $u$ there is $s_u\in S$ with $\mathrm{ham}_{\mathcal P(G,A\cup S)}(u,s_u)\leqslant15(q+1)\beta\gamma$;
--   3. (A3) any two vertices $u,v$ of the same 1-type over $S$ have $\mathrm{ham}_{\mathcal P(G,A\cup S)}(u,v)\leqslant44(q+1)\alpha\gamma$.
--
--   Moreover, assuming that $\mathcal P$ is computable in time $t(n)$, there is an $\mathcal O((\beta+\gamma)|A|(\beta\gamma n^2+t(n)))$-time algorithm computing such $S$ given $q,G,A,\preccurlyeq$. The algorithm is not given $\alpha,\beta,\gamma$.
--
--   This is the first step towards the Damping Theorem: it finds the set $S$, with its properties expressed through Hamming distances rather than a flip.
--
--   **Formalization Note** The constant is absolute. A single run meets (A1)–(A3) and the time bound for every $\alpha,\beta,\gamma\geqslant1$ meeting the hypotheses with this $\preccurlyeq$.
--
--   Differences from the source:
--   - reading: assuming that 𝒫 is computable in time t(n), there is an algorithm → for every program computing 𝒫 within t(n) steps there is a program (which may contain its code), one run good for every α, β, γ meeting the hypotheses; reason: the page says the algorithm is not given α, β, γ, and it must evaluate 𝒫
--   - encoding: 𝒪(E) → c·(E+1) with c absolute; reason: 𝒪 hides constant factors (p.11); +1 only matters where E can be 0
--   - encoding: an algorithm on the RAM model with words of length O(log n) (App. C, p.43) → one program of the published word RAM, correct at every word size above b·(⌊log₂(n + inputs + 2)⌋+1), input in fixed cells, output read by a decoder of the output cells and n; reason: the paper names the model only; the layout is fixed once for all items and the decoders never see the input object
-- source:
--   Dreier, Mählmann, Pilipczuk, Toruńczyk, Monadically Dependent Graph Classes Have Almost Bounded Merge-Width, arXiv:2611.06804 (held version, sha256 6e4b0608…), Lemma 6.1, p.23

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_WordRAM
import Definitions.Def_MonDepMW_RunsWithin
import Definitions.Def_MonDepMW_decodeSet
import Definitions.Def_MonDepMW_PartitionSelector
import Definitions.Def_MonDepMW_PackingLE
import Definitions.Def_MonDepMW_AlternationLE
import Definitions.Def_MonDepMW_IsPredampingSet
import Definitions.Def_MonDepMW_ComputesSelector

set_option autoImplicit false

open TrulySubcubicAPSP

namespace MonDepMW

/-- **Lemma 6.1 (Predamping Lemma).** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), p.23: "Let 𝒫 be a monotone and respectful partition selector, G be a graph, and
α, β, γ ∈ N be such that 𝒫 has growth ratio at most γ on G; G has packing ratio at most β; and G admits a vertex ordering ≼ of
alternation at most α. Then for every q ∈ N and set A ⊆ V (G) with |A| ⩾ 6(q + 1) there exists a set S ⊆ V (G) such that (A1)
|S| ⩽ |A|/q; (A2) for every u ∈ V (G) there exists s_u ∈ S such that ham_{𝒫(G,A∪S)}(u, s_u) ⩽ 15(q + 1) · βγ; and (A3) for any
two vertices u, v ∈ V (G) belonging to the same 1-type over S, we have ham_{𝒫(G,A∪S)}(u, v) ⩽ 44(q + 1) · αγ. Moreover,
assuming that 𝒫 is computable in time t(n), there is an 𝒪((β + γ)|A| · (βγn² + t(n)))-time algorithm computing such a set S
given q, G, A, and ≼. The algorithm does not need to be provided the values of α, β, γ."

**Formalization Note.** `c` is absolute: it precedes `𝔓`, the selector's program and `t`. For every program computing `𝔓`
within `t(n)` there is a program, which may contain the former's code, reading `q`, `G`, `A`, `≼`. Not being given `α, β, γ`, a
single run on an instance meets (A1)–(A3) and the time bound for **every** `α, β, γ ≥ 1` meeting the hypotheses with this `≼`.
Input: `n`, adjacency matrix, `q`, the `n` cells of `A`, the `n` vertices in order. Output: the `n` cells of `S`. -/
theorem lemma_6_1 :
    (∀ (𝔓 : PartitionSelector), 𝔓.Monotone → 𝔓.Respectful → ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (α β γ : ℕ),
      1 ≤ α → 1 ≤ β → 1 ≤ γ → 𝔓.GrowthLE G γ → PackingLE G β → (∃ σ, AlternationLE G σ α) →
      ∀ (q : ℕ), 1 ≤ q → ∀ A : Finset (Fin n), 6 * (q + 1) ≤ A.card →
        ∃ S : Finset (Fin n), IsPredampingSet 𝔓 G A q α β γ S) ∧
    ∃ c : ℕ, ∀ (𝔓 : PartitionSelector), 𝔓.Monotone → 𝔓.Respectful →
      ∀ (Psel : List Instr) (bsel : ℕ) (t : ℕ → ℕ), ComputesSelector 𝔓 Psel bsel t →
      ∃ (P : List Instr) (b : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (q : ℕ), 1 ≤ q →
        ∀ (A : Finset (Fin n)), 6 * (q + 1) ≤ A.card → ∀ (σ : Fin n ≃ Fin n) (W : ℕ),
        b * (Nat.log2 (n + q + 2) + 1) ≤ W → ∀ α β γ : ℕ, 1 ≤ α → 1 ≤ β → 1 ≤ γ →
        𝔓.GrowthLE G γ → PackingLE G β → AlternationLE G σ α →
        RunsWithin P W (c * ((β + γ) * A.card * (β * γ * n ^ 2 + t n) + 1))
          (graphInput G ++ [(q : ℤ)] ++ setBits A ++ orderWords σ) fun out =>
            IsPredampingSet 𝔓 G A q α β γ (decodeSet n out 0) := by sorry

end MonDepMW
