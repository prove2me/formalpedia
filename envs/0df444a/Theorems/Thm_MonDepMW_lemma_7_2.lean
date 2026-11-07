-- Prove2me | Theorems.Thm_MonDepMW_lemma_7_2
-- name    : MonDepMW.lemma_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:51:45.394583+00:00
-- url     : https://prove2.me/theorems/b8d4973e-66fe-4eff-8ee5-91ca0d85b577
-- title:
--   Lemma 7.2 — Symmetrization Lemma
-- statement:
--   Let $G$ be a graph and $\mathcal Q,\mathcal R$ partitions of $V(G)$ with $\mathcal R$ refining $\mathcal Q$. Let $\rho\subseteq\mathcal Q\times\mathcal Q$ have mismatch at most $m$ with respect to $\mathcal R$, for a positive integer $m$. Then there is a symmetric relation $\sigma\subseteq\mathcal Q\times\mathcal Q$ of mismatch at most $3m$ with respect to $\mathcal R$. Moreover, given $G,\mathcal Q,\mathcal R,\rho$, such a $\sigma$ can be computed in time $\mathcal O(n^2)$.
--
--   Relations come from the Predamping Lemma without symmetry, whereas a flip needs it.
--
--   **Formalization Note** $m$ is not an input: a single run serves every $m$ bounding the mismatch of $\rho$. The output is symmetric whatever the mismatch. Relations are $n\times n$ bit matrices indexed by vertices.
--
--   Differences from the source:
--   - encoding: 𝒪(E) → c·(E+1) with c absolute; reason: 𝒪 hides constant factors (p.11); +1 only matters where E can be 0
--   - encoding: an algorithm on the RAM model with words of length O(log n) (App. C, p.43) → one program of the published word RAM, correct at every word size above b·(⌊log₂(n + inputs + 2)⌋+1), input in fixed cells, output read by a decoder of the output cells and n; reason: the paper names the model only; the layout is fixed once for all items and the decoders never see the input object
-- source:
--   Dreier, Mählmann, Pilipczuk, Toruńczyk, Monadically Dependent Graph Classes Have Almost Bounded Merge-Width, arXiv:2611.06804 (held version, sha256 6e4b0608…), Lemma 7.2, p.29

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_WordRAM
import Definitions.Def_MonDepMW_RunsWithin
import Definitions.Def_MonDepMW_decodeSet
import Definitions.Def_MonDepMW_MismatchLE

set_option autoImplicit false

open TrulySubcubicAPSP

namespace MonDepMW

/-- **Lemma 7.2 (Symmetrization Lemma).** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), p.29: "Let G be a graph and 𝒬, ℛ be partitions of the vertex set of G such that
ℛ is a refinement of 𝒬. Let ρ ⊆ 𝒬 × 𝒬 be a relation such that the mismatch of ρ with respect to ℛ is at most m, for some m ∈ N.
Then there is also a symmetric relation σ ⊆ 𝒬 × 𝒬 such that the mismatch of σ with respect to ℛ is at most 3m. Moreover, given
G, 𝒬, ℛ, and ρ, such a relation σ can be computed in time 𝒪(n²)."

**Formalization Note.** `m ∈ N` is `1 ≤ m`. `m` is not an input, so a single run serves every `m` bounding the mismatch of `ρ`.
Input: `n`, adjacency matrix, labels of `𝒬`, labels of `ℛ`, the matrix of `ρ`. Output: the `n × n` matrix of `σ`. -/
theorem lemma_7_2 :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (Q R : Setoid (Fin n)), R ≤ Q →
      ∀ (ρ : Quotient Q → Quotient Q → Prop) (m : ℕ), 1 ≤ m → MismatchLE G Q R ρ m →
        ∃ σ : Quotient Q → Quotient Q → Prop, (∀ X Y, σ X Y → σ Y X) ∧ MismatchLE G Q R σ (3 * m)) ∧
    ∃ (P : List Instr) (b c : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (Q R : Setoid (Fin n)), R ≤ Q →
      ∀ (ρ : Quotient Q → Quotient Q → Prop) (W : ℕ), b * (Nat.log2 (n + 2) + 1) ≤ W →
      RunsWithin P W (c * (n ^ 2 + 1)) (graphInput G ++ partLabels Q ++ partLabels R ++ relMatrix Q ρ) fun out =>
        ∃ σ : Quotient Q → Quotient Q → Prop, EncodesRel out 0 Q σ ∧ (∀ X Y, σ X Y → σ Y X) ∧
          ∀ m : ℕ, 1 ≤ m → MismatchLE G Q R ρ m → MismatchLE G Q R σ (3 * m) := by sorry

end MonDepMW
