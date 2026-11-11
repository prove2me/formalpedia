-- Prove2me | Theorems.Thm_GlobalUpdatesFO_Upper_lemma_4_6
-- name    : GlobalUpdatesFO.Upper.lemma_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:22:30.143889+00:00
-- url     : https://prove2.me/theorems/f379163b-433d-4e76-8110-5329ecca97d2
-- title:
--   Lemma 4.6 — the k-closure of a set of size ≤ h in a structure of treedepth ≤ D has size ≤ a computable f_{4.6}(Σ, h, k, D)
-- statement:
--   There is a computable function $f_{4.6}(\Sigma,h,k,D)$ such that for every $\Sigma$-structure $A$ with $\mathrm{td}(A) \le D$ and every $X \subseteq U(A)$ with $|X| \le h$, the $k$-closure $Y$ of $X$ satisfies
--   $$|Y| \le f_{4.6}(\Sigma,h,k,D).$$
--
--   Bounded closures are what keep the bags of tight decompositions, and hence the flattened signatures, of bounded size.
--
--   Differences from the source:
--   - encoding: a computable function f_{4.6}(Σ, h, k, D) → ∃ f : List ℕ × ℕ × ℕ × ℕ → ℕ computable; reason: 'computable' read as Mathlib Computable on the list codes of signatures (lists of arities) and formulas (prefix codes)
--   - reading: the k-closure of X → every k-closure Y of X (every inclusion-minimal k-robust superset); reason: the k-closure is unique (Corollary 4.4, p. 27), so the two statements are the same
--   - encoding: a finite Σ-structure with universe U(A), relation names of Σ with their arities → Structure σ U on a finite type U : Type, Σ the list of arities, relation names 0, …, |Σ|−1; reason: Lean convention; every finite structure is of this form up to renaming
--   - encoding: Σ^K with symbols R^π for π : [arity(R)] ⇀ K; A^K → flatSig σ |K| (symbol R^π at offset(R) + j, j encoding π in base |K|+1) and flattenAt A K, K named through the enumeration enumOf K; reason: Lean convention; another enumeration of K only renames relation symbols, which changes no type, noble or robust set
-- source:
--   Korhonen, Sokołowski, On efficient global updates in first-order logic, STOC 2027 submission (manuscript sha256 ffb1e749…), p. 28, Lemma 4.6

import Mathlib
import Definitions.Def_GlobalUpdatesFO_Upper_Structure
import Definitions.Def_GlobalUpdatesFO_Upper_Formula
import Definitions.Def_GlobalUpdatesFO_Upper_Flattening
import Definitions.Def_GlobalUpdatesFO_Upper_Robust

namespace GlobalUpdatesFO.Upper

theorem lemma_4_6 :
    ∃ f : List ℕ × ℕ × ℕ × ℕ → ℕ, Computable f ∧
      ∀ (σ : Signature) (h k D : ℕ) (U : Type) [Fintype U] (A : Structure σ U)
        (X Y : Finset U),
        A.td ≤ D → X.card ≤ h → IsClosure k A X Y → Y.card ≤ f (σ, h, k, D) := by sorry

end GlobalUpdatesFO.Upper
