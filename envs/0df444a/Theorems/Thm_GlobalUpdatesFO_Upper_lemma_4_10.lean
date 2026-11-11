-- Prove2me | Theorems.Thm_GlobalUpdatesFO_Upper_lemma_4_10
-- name    : GlobalUpdatesFO.Upper.lemma_4_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:22:02.489197+00:00
-- url     : https://prove2.me/theorems/a60c9df8-db2c-42bf-beec-d0334bd83ca3
-- title:
--   Lemma 4.10 — an interpretation keeping treedepth ≤ D adds no edge between two components of A^K for a k-robust K
-- statement:
--   For all $\nu, D \ge 1$ there is a computable integer $k' = k_{4.10}(\nu,D)$ such that: let $\Sigma, \Pi$ be signatures with $\mathrm{maxarity}(\Sigma), \mathrm{maxarity}(\Pi) \le \nu$, $A$ a $\Sigma$-structure, $k \ge k'$, $K \subseteq U(A)$ a $k$-robust set in $A$, $C_1, C_2$ two distinct connected components of $A^K$ and $I$ a $k$-bounded $(\Sigma,\Pi)$-interpretation. If $\mathrm{td}(A) \le D$ and $\mathrm{td}(I(A)) \le D$, then $G(I(A))$ has no edge between a vertex of $C_1$ and a vertex of $C_2$.
--
--   This locality statement is what lets a global update be processed component by component of the flattened structure.
--
--   **Formalization Note** "Vertices of two distinct components of $A^K$" are elements $x, y$ of $U(A) \setminus K$ that are not reachable from each other in $G(A^K)$.
--
--   Differences from the source:
--   - encoding: a computable integer k′ = k_{4.10}(ν, D) → ∃ k410 : ℕ × ℕ → ℕ computable; reason: 'computable' read as Mathlib Computable on the list codes of signatures (lists of arities) and formulas (prefix codes)
--   - encoding: u ∈ C_1, v ∈ C_2 for distinct components C_1, C_2 of A^K → x, y : {u // u ∉ K} with ¬ (flattenAt A K).gaifman.Reachable x y; reason: two elements lie in distinct components iff they are not reachable from each other
--   - encoding: a finite Σ-structure with universe U(A), relation names of Σ with their arities → Structure σ U on a finite type U : Type, Σ the list of arities, relation names 0, …, |Σ|−1; reason: Lean convention; every finite structure is of this form up to renaming
--   - encoding: Σ^K with symbols R^π for π : [arity(R)] ⇀ K; A^K → flatSig σ |K| (symbol R^π at offset(R) + j, j encoding π in base |K|+1) and flattenAt A K, K named through the enumeration enumOf K; reason: Lean convention; another enumeration of K only renames relation symbols, which changes no type, noble or robust set
-- source:
--   Korhonen, Sokołowski, On efficient global updates in first-order logic, STOC 2027 submission (manuscript sha256 ffb1e749…), p. 30, Lemma 4.10

import Mathlib
import Definitions.Def_GlobalUpdatesFO_Upper_Structure
import Definitions.Def_GlobalUpdatesFO_Upper_Formula
import Definitions.Def_GlobalUpdatesFO_Upper_Flattening
import Definitions.Def_GlobalUpdatesFO_Upper_Robust

namespace GlobalUpdatesFO.Upper

theorem lemma_4_10 :
    ∃ k410 : ℕ × ℕ → ℕ, Computable k410 ∧
      ∀ (ν D : ℕ), 1 ≤ ν → 1 ≤ D → ∀ σ π : Signature, σ.maxarity ≤ ν → π.maxarity ≤ ν →
        ∀ (U : Type) [Fintype U] (A : Structure σ U) (k : ℕ), k410 (ν, D) ≤ k →
          ∀ K : Finset U, IsRobust k A K →
          ∀ I : Interp σ π, I.IsKBounded k → A.td ≤ D → (I.apply A).td ≤ D →
            ∀ x y : {u : U // u ∉ Set.range (enumOf K)},
              ¬ (flattenAt A K).gaifman.Reachable x y →
                ¬ (I.apply A).gaifman.Adj x.val y.val := by sorry

end GlobalUpdatesFO.Upper
