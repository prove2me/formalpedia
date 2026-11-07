-- Prove2me | Theorems.Thm_MonDepMW_corollary_7_8
-- name    : MonDepMW.corollary_7_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:53:18.15549+00:00
-- url     : https://prove2.me/theorems/974cf77a-bff2-4e89-9cce-ba1a13fe0a0c
-- title:
--   Corollary 7.8 — a symmetric relation of small mismatch
-- statement:
--   Let $\mathcal P$ be a monotone and respectful partition selector, $G$ a graph, and $\alpha,\beta,\gamma\geqslant1$ such that $\mathcal P$ has growth ratio at most $\gamma$ on $G$, $G$ has packing ratio at most $\beta$, and $G$ admits a vertex ordering $\preccurlyeq$ of alternation at most $\alpha$. Then for every $q\geqslant1$ and non-empty $A\subseteq V(G)$ there are a set $S$ with $|S|\leqslant|A|/q$ and a symmetric relation $\sigma\subseteq\mathcal T_1(G,S)\times\mathcal T_1(G,S)$ whose mismatch with respect to $\mathcal P(G,A\cup S)$ is at most
--   $$264q(\alpha+\beta)\gamma.$$
--   Moreover, assuming that $\mathcal P$ is computable in time $t(n)$, there is an $\mathcal O((\beta+\gamma)|A|(\beta\gamma n^2+t(n)))$-time algorithm computing such $S$ and $\sigma$, given $q,G,A,\preccurlyeq$.
--
--   The relation $\sigma$ is the flip of the Damping Theorem.
--
--   **Formalization Note** The constant is absolute, chosen before the selector and its program. Output: the bits of $S$, then the $n\times n$ bit matrix of $\sigma$ indexed by vertices.
--
--   Differences from the source:
--   - reading: assuming that 𝒫 is computable in time t(n), there is an algorithm → for every program computing 𝒫 within t(n) steps there is a program (which may contain its code), one run good for every α, β, γ meeting the hypotheses; reason: the algorithm is not given α, β, γ (Lemma 6.1’s last sentence), and the algorithm must evaluate 𝒫
--   - encoding: 𝒪(E) → c·(E+1) with c absolute; reason: 𝒪 hides constant factors (p.11); +1 only matters where E can be 0
--   - encoding: an algorithm on the RAM model with words of length O(log n) (App. C, p.43) → one program of the published word RAM, correct at every word size above b·(⌊log₂(n + inputs + 2)⌋+1), input in fixed cells, output read by a decoder of the output cells and n; reason: the paper names the model only; the layout is fixed once for all items and the decoders never see the input object
-- source:
--   Dreier, Mählmann, Pilipczuk, Toruńczyk, Monadically Dependent Graph Classes Have Almost Bounded Merge-Width, arXiv:2611.06804 (held version, sha256 6e4b0608…), Corollary 7.8, p.32

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_WordRAM
import Definitions.Def_MonDepMW_RunsWithin
import Definitions.Def_MonDepMW_decodeSet
import Definitions.Def_MonDepMW_PartitionSelector
import Definitions.Def_MonDepMW_PackingLE
import Definitions.Def_MonDepMW_AlternationLE
import Definitions.Def_MonDepMW_MismatchLE
import Definitions.Def_MonDepMW_ComputesSelector

set_option autoImplicit false

open TrulySubcubicAPSP

namespace MonDepMW

/-- **Corollary 7.8.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), p.32: "Let 𝒫 be a monotone and respectful partition selector, G be a graph, and α, β, γ ∈ N be such
that 𝒫 has growth ratio at most γ on G; G has packing ratio at most β; and G admits a vertex ordering ≼ of alternation at most
α. Then for every q ∈ N and non-empty set A ⊆ V (G) there exists a set S ⊆ V (G) with |S| ⩽ |A|/q and a symmetric relation
σ ⊆ 𝒯1(G, S) × 𝒯1(G, S) such that the mismatch of σ with respect to 𝒫(G, A ∪ S) is at most 264q · (α + β)γ. Moreover, assuming
that 𝒫 is computable in time t(n), there is an 𝒪((β + γ)|A| · (βγn² + t(n)))-time algorithm computing such a set S and relation
σ, given q, G, A, and ≼."

**Formalization Note.** The algorithmic clause has the same shape as in Lemma 6.1: `c` absolute, one run good for every
`α, β, γ` meeting the hypotheses. `𝔓(G, A ∪ S)` refines `𝒯₁(G, S)` by respectfulness and monotonicity of `𝒯₁`. Input as in
Lemma 6.1. Output: the `n` cells of `S`, then the `n × n` matrix of `σ`, indexed by vertices. -/
theorem corollary_7_8 :
    (∀ (𝔓 : PartitionSelector), 𝔓.Monotone → 𝔓.Respectful → ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (α β γ : ℕ),
      1 ≤ α → 1 ≤ β → 1 ≤ γ → 𝔓.GrowthLE G γ → PackingLE G β → (∃ σ, AlternationLE G σ α) →
      ∀ (q : ℕ), 1 ≤ q → ∀ A : Finset (Fin n), A.Nonempty →
        ∃ (S : Finset (Fin n)) (σ : Quotient (oneType G S) → Quotient (oneType G S) → Prop),
          (S.card : ℝ) ≤ (A.card : ℝ) / (q : ℝ) ∧ (∀ X Y, σ X Y → σ Y X) ∧
          MismatchLE G (oneType G S) (𝔓 n G (A ∪ S)) σ (264 * q * ((α + β) * γ))) ∧
    ∃ c : ℕ, ∀ (𝔓 : PartitionSelector), 𝔓.Monotone → 𝔓.Respectful →
      ∀ (Psel : List Instr) (bsel : ℕ) (t : ℕ → ℕ), ComputesSelector 𝔓 Psel bsel t →
      ∃ (P : List Instr) (b : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (q : ℕ), 1 ≤ q →
        ∀ (A : Finset (Fin n)), A.Nonempty → ∀ (τ : Fin n ≃ Fin n) (W : ℕ),
        b * (Nat.log2 (n + q + 2) + 1) ≤ W → ∀ α β γ : ℕ, 1 ≤ α → 1 ≤ β → 1 ≤ γ →
        𝔓.GrowthLE G γ → PackingLE G β → AlternationLE G τ α →
        RunsWithin P W (c * ((β + γ) * A.card * (β * γ * n ^ 2 + t n) + 1))
          (graphInput G ++ [(q : ℤ)] ++ setBits A ++ orderWords τ) fun out =>
            ((decodeSet n out 0).card : ℝ) ≤ (A.card : ℝ) / (q : ℝ) ∧
            ∃ σ : Quotient (oneType G (decodeSet n out 0)) → Quotient (oneType G (decodeSet n out 0)) → Prop,
              EncodesRel out n (oneType G (decodeSet n out 0)) σ ∧ (∀ X Y, σ X Y → σ Y X) ∧
              MismatchLE G (oneType G (decodeSet n out 0)) (𝔓 n G (A ∪ decodeSet n out 0)) σ
                (264 * q * ((α + β) * γ)) := by sorry

end MonDepMW
