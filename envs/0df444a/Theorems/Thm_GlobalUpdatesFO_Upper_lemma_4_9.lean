-- Prove2me | Theorems.Thm_GlobalUpdatesFO_Upper_lemma_4_9
-- name    : GlobalUpdatesFO.Upper.lemma_4_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:22:11.290232+00:00
-- url     : https://prove2.me/theorems/b4030efa-ddac-4fd8-828e-819071b7e09f
-- title:
--   Lemma 4.9 — k-robust sets stay k-robust under k-bounded interpretations
-- statement:
--   Let $A$ be a $\Sigma$-structure, $K \subseteq U(A)$ a $k$-robust set and $I$ a $k$-bounded $(\Sigma,\Pi)$-interpretation. Then $K$ is a $k$-robust set in $I(A)$:
--   $$(I(A))^K \text{ has no } k\text{-nobles}.$$
--
--   Consequently the $k$-closure of a set can only shrink under a global update, which the potential argument of the paper exploits.
--
--   Differences from the source:
--   - encoding: a finite Σ-structure with universe U(A), relation names of Σ with their arities → Structure σ U on a finite type U : Type, Σ the list of arities, relation names 0, …, |Σ|−1; reason: Lean convention; every finite structure is of this form up to renaming
--   - encoding: Σ^K with symbols R^π for π : [arity(R)] ⇀ K; A^K → flatSig σ |K| (symbol R^π at offset(R) + j, j encoding π in base |K|+1) and flattenAt A K, K named through the enumeration enumOf K; reason: Lean convention; another enumeration of K only renames relation symbols, which changes no type, noble or robust set
-- source:
--   Korhonen, Sokołowski, On efficient global updates in first-order logic, STOC 2027 submission (manuscript sha256 ffb1e749…), p. 29, Lemma 4.9

import Mathlib
import Definitions.Def_GlobalUpdatesFO_Upper_Structure
import Definitions.Def_GlobalUpdatesFO_Upper_Formula
import Definitions.Def_GlobalUpdatesFO_Upper_Flattening
import Definitions.Def_GlobalUpdatesFO_Upper_Robust

namespace GlobalUpdatesFO.Upper

theorem lemma_4_9 (σ π : Signature) (k : ℕ) (U : Type) [Fintype U] (A : Structure σ U)
    (K : Finset U) (I : Interp σ π) (hK : IsRobust k A K) (hI : I.IsKBounded k) :
    IsRobust k (I.apply A) K := by sorry

end GlobalUpdatesFO.Upper
