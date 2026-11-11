-- Prove2me | Theorems.Thm_MultiCorrectPAC_Demo_lemma_8
-- name    : MultiCorrectPAC.Demo.lemma_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:45:39.228852+00:00
-- url     : https://prove2.me/theorems/ca889ff4-544d-41cb-9787-f53d84a87d2a
-- title:
--   Lemma 8 — an empty-intersection family of sets of size at most ℓ has an empty-intersection subfamily of at most ℓ + 1 members
-- statement:
--   Let $\ell\ge1$ and let $\mathcal Y$ be a nonempty set. If a family of nonempty sets of at most $\ell$ labels has empty intersection, then some subfamily of at most $\ell+1$ members has empty intersection. Consequently every minimal empty-intersection family of such sets has between two and $\ell+1$ members:
--   $$\bigcap\mathcal F=\emptyset\ \Rightarrow\ \exists\,\mathcal F'\subseteq\mathcal F,\ |\mathcal F'|\le\ell+1,\ \bigcap\mathcal F'=\emptyset;\qquad \mathcal F\text{ minimal}\Rightarrow 2\le|\mathcal F|\le\ell+1.$$
--
--   This Helly-type fact is what makes $\ell+1$ the right number of hypotheses to intersect: it underlies the comparison of the dimensions (Lemma 9), the potential argument of Section 7 and the $d=0$ case of Theorem 41.
--
--   Differences from the source:
--   - encoding: a family of nonempty sets of size at most ℓ (possibly infinite) → 𝒜 : Set (Finset Y) with every member satisfying InA ℓ; the subfamily is a Finset; a minimal family is a Finset (Finset Y) (minimal families are finite by definition); reason: Lean convention
--   - encoding: Y nonempty, ℓ ≥ 1 (standing, §5.1) → [Nonempty Y], hℓ : 1 ≤ ℓ; reason: standing assumptions made explicit; without Y ≠ ∅ the empty family would be a minimal empty-intersection family
--   - generalization: X and Y nonempty countable sets (§5.1, p. 25) → Y : Type* any nonempty type, not required countable; reason: a statement about families of finite sets that never uses countability; on a countable Y it is the paper's statement
-- source:
--   Hanneke, Mansouri, Pour, Shaeiri, Wang, PAC Learning with Multiple Correct Answers, STOC 2027 submission (manuscript sha256 2844bd34…), pp. 30–31 (PDF 32–33), Lemma 8

import Mathlib
import Definitions.Def_MultiCorrectPAC_Demo_Hypotheses
import Definitions.Def_MultiCorrectPAC_Demo_Dimensions

open scoped ENNReal

namespace MultiCorrectPAC.Demo

theorem lemma_8 (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {Y : Type*} [Nonempty Y] :
    (∀ 𝒜 : Set (Finset Y), (∀ A ∈ 𝒜, InA ℓ A) → EmptyInter 𝒜 →
      ∃ 𝒜' : Finset (Finset Y), (↑𝒜' : Set (Finset Y)) ⊆ 𝒜 ∧ 𝒜'.card ≤ ℓ + 1 ∧
        EmptyInter (↑𝒜' : Set (Finset Y))) ∧
    (∀ 𝒜 : Finset (Finset Y), (∀ A ∈ 𝒜, InA ℓ A) → IsMinimalEmptyInter 𝒜 →
      2 ≤ 𝒜.card ∧ 𝒜.card ≤ ℓ + 1) := by sorry

end MultiCorrectPAC.Demo
