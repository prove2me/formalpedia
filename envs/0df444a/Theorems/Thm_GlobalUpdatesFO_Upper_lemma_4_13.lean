-- Prove2me | Theorems.Thm_GlobalUpdatesFO_Upper_lemma_4_13
-- name    : GlobalUpdatesFO.Upper.lemma_4_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:22:22.098189+00:00
-- url     : https://prove2.me/theorems/a683ab07-9d5f-4541-8f5b-2b35fbaa9e2e
-- title:
--   Lemma 4.13 — every k-robust set is a prefix of the tight k-robust decomposition
-- statement:
--   Let $\nu, k, D \ge 1$ with $k \ge k_{4.11}(\nu,D)$, $\Sigma$ a signature with $\mathrm{maxarity}(\Sigma) \le \nu$, $A$ a $\Sigma$-structure with $\mathrm{td}(A) \le D$ and $\mathcal F_{\mathrm{tight}}$ the tight $k$-robust decomposition of $A$. Every $k$-robust set $W$ of $A$ is a prefix of $\mathcal F_{\mathrm{tight}}$: it is the union of the bags of an ancestor-closed set of nodes.
--
--   Robust sets, the objects updates naturally produce, are therefore always visible in the tight decomposition as a top part of it.
--
--   Differences from the source:
--   - reading: k ≥ k_{4.11}(ν, D), the threshold of Lemma 4.11 → k ≥ k′(ν, D) for a computable k′ existentially quantified in this lemma; reason: k_{4.11} is only defined by the existential of Lemma 4.11; all these thresholds are monotone (they hold for every larger k), so one joint threshold exists iff each lemma has its own
--   - reading: F_tight, the tight k-robust decomposition of A → every tight k-robust decomposition F of A; reason: the tight decomposition is unique up to renaming nodes (Lemma 4.11), and being a prefix is invariant under such renaming
--   - encoding: a finite Σ-structure with universe U(A), relation names of Σ with their arities → Structure σ U on a finite type U : Type, Σ the list of arities, relation names 0, …, |Σ|−1; reason: Lean convention; every finite structure is of this form up to renaming
--   - encoding: Σ^K with symbols R^π for π : [arity(R)] ⇀ K; A^K → flatSig σ |K| (symbol R^π at offset(R) + j, j encoding π in base |K|+1) and flattenAt A K, K named through the enumeration enumOf K; reason: Lean convention; another enumeration of K only renames relation symbols, which changes no type, noble or robust set
-- source:
--   Korhonen, Sokołowski, On efficient global updates in first-order logic, STOC 2027 submission (manuscript sha256 ffb1e749…), p. 33, Lemma 4.13

import Mathlib
import Definitions.Def_GlobalUpdatesFO_Upper_Structure
import Definitions.Def_GlobalUpdatesFO_Upper_Formula
import Definitions.Def_GlobalUpdatesFO_Upper_Flattening
import Definitions.Def_GlobalUpdatesFO_Upper_Robust

namespace GlobalUpdatesFO.Upper

theorem lemma_4_13 :
    ∃ k' : ℕ × ℕ → ℕ, Computable k' ∧
      ∀ (ν k D : ℕ), 1 ≤ ν → 1 ≤ k → 1 ≤ D → k' (ν, D) ≤ k →
        ∀ σ : Signature, σ.maxarity ≤ ν →
          ∀ (U : Type) [Fintype U] (A : Structure σ U), A.td ≤ D →
            ∀ (N : Type) [Fintype N] (F : Decomp U N), Decomp.IsTight k A F →
              ∀ W : Finset U, IsRobust k A W → F.IsPrefix (W : Set U) := by sorry

end GlobalUpdatesFO.Upper
