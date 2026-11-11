-- Prove2me | Theorems.Thm_GlobalUpdatesFO_Upper_lemma_4_1
-- name    : GlobalUpdatesFO.Upper.lemma_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:22:09.238616+00:00
-- url     : https://prove2.me/theorems/cb4215ad-7c5e-4560-b6b5-4fa93d8394ef
-- title:
--   Lemma 4.1 — removing the k-nobles of a nonempty connected structure of treedepth ≤ D strictly decreases treedepth, for k ≥ a computable k_{4.1}(ν, D)
-- statement:
--   For all $\nu, D \ge 1$ there is a computable integer $k' = k_{4.1}(\nu,D)$ such that: if $\Sigma$ is a signature with $\mathrm{maxarity}(\Sigma) \le \nu$, $A$ is a nonempty connected $\Sigma$-structure with $\mathrm{td}(A) \le D$, $k \ge k'$ and $K$ is the set of $k$-nobles of $A$, then
--   $$\mathrm{td}(G(A) \setminus K) < \mathrm{td}(G(A)) .$$
--
--   In particular a nonempty connected structure of bounded treedepth always has a $k$-noble; this is what makes the root bags of tight decompositions nonempty and their depth at most $D$.
--
--   **Formalization Note** $G(A) \setminus K$ is the subgraph of $G(A)$ induced by the $k$-common elements. "Nonempty connected" is Mathlib's `SimpleGraph.Connected`, which includes nonemptiness.
--
--   Differences from the source:
--   - encoding: a computable integer k′ = k_{4.1}(ν, D) → ∃ k41 : ℕ × ℕ → ℕ computable, quantified before ν, D, Σ and A; reason: 'computable' read as Mathlib Computable on the list codes of signatures (lists of arities) and formulas (prefix codes)
--   - encoding: G(A) \ K for K the set of k-nobles → tdInduce A.gaifman {u | IsCommon k A u}; reason: removing the nobles leaves the subgraph induced by the commons
--   - encoding: a finite Σ-structure with universe U(A), relation names of Σ with their arities → Structure σ U on a finite type U : Type, Σ the list of arities, relation names 0, …, |Σ|−1; reason: Lean convention; every finite structure is of this form up to renaming
-- source:
--   Korhonen, Sokołowski, On efficient global updates in first-order logic, STOC 2027 submission (manuscript sha256 ffb1e749…), p. 26, Lemma 4.1

import Mathlib
import Definitions.Def_GlobalUpdatesFO_Upper_Structure
import Definitions.Def_GlobalUpdatesFO_Upper_Formula
import Definitions.Def_GlobalUpdatesFO_Upper_Flattening
import Definitions.Def_GlobalUpdatesFO_Upper_Robust

namespace GlobalUpdatesFO.Upper

theorem lemma_4_1 :
    ∃ k41 : ℕ × ℕ → ℕ, Computable k41 ∧
      ∀ (ν D : ℕ), 1 ≤ ν → 1 ≤ D → ∀ σ : Signature, σ.maxarity ≤ ν →
        ∀ (U : Type) [Fintype U] (A : Structure σ U), A.gaifman.Connected → A.td ≤ D →
          ∀ k : ℕ, k41 (ν, D) ≤ k →
            tdInduce A.gaifman {u | IsCommon k A u} < A.td := by sorry

end GlobalUpdatesFO.Upper
