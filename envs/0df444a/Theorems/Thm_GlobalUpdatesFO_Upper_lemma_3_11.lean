-- Prove2me | Theorems.Thm_GlobalUpdatesFO_Upper_lemma_3_11
-- name    : GlobalUpdatesFO.Upper.lemma_3_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:21:35.906186+00:00
-- url     : https://prove2.me/theorems/dac6376b-5ad7-4d01-91a3-6cffcb1e67bc
-- title:
--   Lemma 3.11 — a k-bounded interpretation commutes with flattening: I_K(A^K) = (I(A))^K, with I_K computable from I and K
-- statement:
--   Let $k \ge 1$, let $I$ be a $k$-bounded $(\Sigma,\Pi)$-interpretation and $K$ a finite set. One can compute from $I$ and $K$ a $k$-bounded $(\Sigma^K,\Pi^K)$-interpretation $I_K$ such that for every $\Sigma$-structure $A$ with $K \subseteq U(A)$,
--   $$I_K(A^K) = (I(A))^K .$$
--
--   The lemma lets the data structure apply a global update to a flattened structure directly, without reconstructing the original.
--
--   **Formalization Note** $K$ has $m$ elements and enters through an injective enumeration $\kappa : \{0,\dots,m-1\} \to U(A)$; the symbols of $\Sigma^K$ and $\Pi^K$ name elements of $K$ by their index, so $I_K$ is computed from the signatures, the code of $I$ and $m$, and the identity holds for every structure and every enumeration.
--
--   Differences from the source:
--   - encoding: we can compute I_K from I and K → ∃ F computable on List ℕ × List ℕ × List ℕ × ℕ with F(Σ, Π, code of I, |K|) = code of I_K; reason: 'computable' read as Mathlib Computable on the list codes of signatures (lists of arities) and formulas (prefix codes)
--   - encoding: a finite set K with K ⊆ U(A); Σ^K, Π^K, A^K → an injective κ : Fin m → U; flatSig σ m, flatSig π m and flatten A κ; reason: Lean convention; the paper's symbols R^π name elements of K, here by their index in the enumeration
--   - encoding: a finite Σ-structure with universe U(A), relation names of Σ with their arities → Structure σ U on a finite type U : Type, Σ the list of arities, relation names 0, …, |Σ|−1; reason: Lean convention; every finite structure is of this form up to renaming
-- source:
--   Korhonen, Sokołowski, On efficient global updates in first-order logic, STOC 2027 submission (manuscript sha256 ffb1e749…), p. 23, Lemma 3.11

import Mathlib
import Definitions.Def_GlobalUpdatesFO_Upper_Structure
import Definitions.Def_GlobalUpdatesFO_Upper_Formula
import Definitions.Def_GlobalUpdatesFO_Upper_Flattening

namespace GlobalUpdatesFO.Upper

theorem lemma_3_11 :
    ∃ F : List ℕ × List ℕ × List ℕ × ℕ → List ℕ, Computable F ∧
      ∀ (σ π : Signature) (k : ℕ) (I : Interp σ π) (m : ℕ), 1 ≤ k → I.IsKBounded k →
        ∃ IK : Interp (flatSig σ m) (flatSig π m),
          F (σ, π, I.code, m) = IK.code ∧ IK.IsKBounded k ∧
          ∀ (U : Type) [Fintype U] (A : Structure σ U) (κ : Fin m → U), Function.Injective κ →
            IK.apply (flatten A κ) = flatten (I.apply A) κ := by sorry

end GlobalUpdatesFO.Upper
