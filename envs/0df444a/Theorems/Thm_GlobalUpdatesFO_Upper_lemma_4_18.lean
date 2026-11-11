-- Prove2me | Theorems.Thm_GlobalUpdatesFO_Upper_lemma_4_18
-- name    : GlobalUpdatesFO.Upper.lemma_4_18
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:22:05.379194+00:00
-- url     : https://prove2.me/theorems/35f03f0d-f4bc-47d2-b36c-43a942e36da3
-- title:
--   Lemma 4.18 — on a connected structure, a k-robust decomposition stays k-robust after a k-bounded interpretation that keeps treedepth ≤ D
-- statement:
--   Let $\nu, k, D \ge 1$ with $k \ge k_{4.10}(\nu,D)$, $\Sigma, \Pi$ signatures with $\mathrm{maxarity}(\Sigma), \mathrm{maxarity}(\Pi) \le \nu$, $A$ a connected $\Sigma$-structure with $\mathrm{td}(A) \le D$, $\mathcal F$ a $k$-robust decomposition of $A$ and $I$ a $k$-bounded $(\Sigma,\Pi)$-interpretation with $\mathrm{td}(I(A)) \le D$. Then
--   $$\mathcal F \text{ is also a } k\text{-robust decomposition of } I(A).$$
--
--   The paper shows by example (two isolated vertices made adjacent) that connectedness cannot be dropped.
--
--   Differences from the source:
--   - reading: k ≥ k_{4.10}(ν, D), the threshold of Lemma 4.10 → k ≥ k′(ν, D) for a computable k′ existentially quantified in this lemma; reason: k_{4.10} is only defined by the existential of Lemma 4.10; all these thresholds are monotone (they hold for every larger k), so one joint threshold exists iff each lemma has its own
--   - generalization: A a connected Σ-structure → A.gaifman.Preconnected (connected, or empty); reason: for the empty structure the only decomposition is the empty one, robust for I(A) as well; for nonempty A preconnected is connected, so the statement specializes to the paper's
--   - encoding: a finite Σ-structure with universe U(A), relation names of Σ with their arities → Structure σ U on a finite type U : Type, Σ the list of arities, relation names 0, …, |Σ|−1; reason: Lean convention; every finite structure is of this form up to renaming
--   - encoding: Σ^K with symbols R^π for π : [arity(R)] ⇀ K; A^K → flatSig σ |K| (symbol R^π at offset(R) + j, j encoding π in base |K|+1) and flattenAt A K, K named through the enumeration enumOf K; reason: Lean convention; another enumeration of K only renames relation symbols, which changes no type, noble or robust set
-- source:
--   Korhonen, Sokołowski, On efficient global updates in first-order logic, STOC 2027 submission (manuscript sha256 ffb1e749…), p. 36, Lemma 4.18

import Mathlib
import Definitions.Def_GlobalUpdatesFO_Upper_Structure
import Definitions.Def_GlobalUpdatesFO_Upper_Formula
import Definitions.Def_GlobalUpdatesFO_Upper_Flattening
import Definitions.Def_GlobalUpdatesFO_Upper_Robust

namespace GlobalUpdatesFO.Upper

theorem lemma_4_18 :
    ∃ k' : ℕ × ℕ → ℕ, Computable k' ∧
      ∀ (ν k D : ℕ), 1 ≤ ν → 1 ≤ k → 1 ≤ D → k' (ν, D) ≤ k →
        ∀ σ π : Signature, σ.maxarity ≤ ν → π.maxarity ≤ ν →
          ∀ (U : Type) [Fintype U] (A : Structure σ U), A.gaifman.Preconnected → A.td ≤ D →
            ∀ (N : Type) (F : Decomp U N), Decomp.IsRobustDecomp k A F →
              ∀ I : Interp σ π, I.IsKBounded k → (I.apply A).td ≤ D →
                Decomp.IsRobustDecomp k (I.apply A) F := by sorry

end GlobalUpdatesFO.Upper
