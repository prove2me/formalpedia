-- Prove2me | Theorems.Thm_GlobalUpdatesFO_Upper_lemma_4_11
-- name    : GlobalUpdatesFO.Upper.lemma_4_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:22:12.846759+00:00
-- url     : https://prove2.me/theorems/63756f30-e340-448e-899e-b5feb9444081
-- title:
--   Lemma 4.11 — the tight k-robust decomposition exists, is unique, has depth ≤ D and bags of size ≤ a computable f_{4.11}(Σ, k, D)
-- statement:
--   For all $\nu, D \ge 1$ there is a computable integer $k' = k_{4.11}(\nu,D)$ such that: let $\Sigma$ be a signature with $\mathrm{maxarity}(\Sigma) \le \nu$, $A$ a $\Sigma$-structure with $\mathrm{td}(G(A)) \le D$ and $k \ge k'$. Then a tight $k$-robust decomposition of $A$ exists, is unique, and has depth at most $D$. Moreover each of its bags has size at most $f_{4.11}(\Sigma,k,D)$ for a computable function $f_{4.11}$:
--   $$\exists!\ \mathcal F \text{ tight},\qquad \mathrm{depth}(\mathcal F) \le D,\qquad |\mathrm{bag}(t)| \le f_{4.11}(\Sigma,k,D).$$
--
--   The tight decomposition is the canonical structure the data structure maintains.
--
--   **Formalization Note** Uniqueness is uniqueness up to renaming the nodes: any two tight $k$-robust decompositions put the same elements in a common bag and have the same ancestor relation between the bags of any two elements. The depth and bag bounds are stated for every tight decomposition.
--
--   Differences from the source:
--   - encoding: a computable integer k′ = k_{4.11}(ν, D) and a computable function f_{4.11}(Σ, k, D) → ∃ k411 : ℕ × ℕ → ℕ and f411 : List ℕ × ℕ × ℕ → ℕ, both computable; reason: 'computable' read as Mathlib Computable on the list codes of signatures (lists of arities) and formulas (prefix codes)
--   - reading: the tight k-robust decomposition is unique → any two tight decompositions F₁, F₂ satisfy, for all u, v: same bag in F₁ ↔ same bag in F₂, and ancestor in F₁ ↔ ancestor in F₂; reason: a decomposition is determined only up to renaming its forest nodes
--   - reading: has depth at most D; each bag of this decomposition has size at most f_{4.11} → every tight k-robust decomposition has depth ≤ D and bags of size ≤ f411(σ, k, D); reason: by uniqueness 'this decomposition' is any tight one
--   - encoding: a decomposition (F, bag) with nonempty disjoint bags covering U(A) → Decomp U N: a RootedForest on N with a surjective bagOf : U → N; reason: bags are the fibres of bag⁻¹
--   - encoding: a finite Σ-structure with universe U(A), relation names of Σ with their arities → Structure σ U on a finite type U : Type, Σ the list of arities, relation names 0, …, |Σ|−1; reason: Lean convention; every finite structure is of this form up to renaming
--   - encoding: Σ^K with symbols R^π for π : [arity(R)] ⇀ K; A^K → flatSig σ |K| (symbol R^π at offset(R) + j, j encoding π in base |K|+1) and flattenAt A K, K named through the enumeration enumOf K; reason: Lean convention; another enumeration of K only renames relation symbols, which changes no type, noble or robust set
-- source:
--   Korhonen, Sokołowski, On efficient global updates in first-order logic, STOC 2027 submission (manuscript sha256 ffb1e749…), p. 31, Lemma 4.11

import Mathlib
import Definitions.Def_GlobalUpdatesFO_Upper_Structure
import Definitions.Def_GlobalUpdatesFO_Upper_Formula
import Definitions.Def_GlobalUpdatesFO_Upper_Flattening
import Definitions.Def_GlobalUpdatesFO_Upper_Robust

namespace GlobalUpdatesFO.Upper

theorem lemma_4_11 :
    ∃ (k411 : ℕ × ℕ → ℕ) (f411 : List ℕ × ℕ × ℕ → ℕ), Computable k411 ∧ Computable f411 ∧
      ∀ (ν D : ℕ), 1 ≤ ν → 1 ≤ D → ∀ σ : Signature, σ.maxarity ≤ ν →
        ∀ (U : Type) [Fintype U] (A : Structure σ U), A.td ≤ D →
          ∀ k : ℕ, k411 (ν, D) ≤ k →
            (∃ (N : Type) (_ : Fintype N) (F : Decomp U N), Decomp.IsTight k A F) ∧
            (∀ (N : Type) [Fintype N] (F : Decomp U N), Decomp.IsTight k A F →
              F.depth ≤ D ∧ ∀ t : N, (F.bag t).ncard ≤ f411 (σ, k, D)) ∧
            (∀ (N₁ N₂ : Type) [Fintype N₁] [Fintype N₂] (F₁ : Decomp U N₁) (F₂ : Decomp U N₂),
              Decomp.IsTight k A F₁ → Decomp.IsTight k A F₂ →
              ∀ u v : U, (F₁.bagOf u = F₁.bagOf v ↔ F₂.bagOf u = F₂.bagOf v) ∧
                (F₁.forest.IsAncestor (F₁.bagOf u) (F₁.bagOf v) ↔
                  F₂.forest.IsAncestor (F₂.bagOf u) (F₂.bagOf v))) := by sorry

end GlobalUpdatesFO.Upper
