-- Prove2me | Theorems.Thm_MMSDelta2_Supplement_theorem_1_3
-- name    : MMSDelta2.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:08:43.804966+00:00
-- url     : https://prove2.me/theorems/cfec178b-7469-4c1a-8e4a-cbb6c9d927c4
-- title:
--   Theorem 1.3 — MMS existence is strongly co-NP-hard, even with two agent types
-- statement:
--   Consider additive goods instances with $n\ge 1$ agents and nonnegative values. Deciding whether such an instance admits an MMS allocation is **strongly** co-NP-hard: there is a polynomial $p(\ell)=\ell^k+k$ such that the problem restricted to instances whose values are integers of absolute value at most $p(\ell)$, $\ell$ the length of the instance, is co-NP-hard. The same holds, with some polynomial, for instances with only two agent types:
--   $$\exists k:\ \mathrm{MMS\text{-}Goods}\big|_{\,k\text{-bounded}}\ \text{is co-NP-hard},\qquad \exists k:\ \mathrm{MMS\text{-}Goods}\big|_{\,k\text{-bounded},\ \mathrm{numTypes}(v)\le 2}\ \text{is co-NP-hard}.$$
--   The number of agents is not restricted.
--
--   With a single agent type an MMS allocation always exists, so this is a sharp dichotomy in the number of agent types; the bounded values also give the no-FPTAS result for the optimal MMS ratio (Corollary 1.4).
--
--   **Formalization Note** "$k$-bounded" is `IntBounded k`: every value is an integer of absolute value at most $\ell^k+k$, $\ell$ the length of the base `instCode` of the instance. Instances outside the restricted class are not in the language.
--
--   Differences from the source:
--   - reading: "strongly co-NP-hard" → for some k, co-NP-hardness of the restriction to instances whose values are integers bounded by ℓ^k + k (ℓ the code length); reason: p.3 defines it as hardness "even when all numerical values are given in unary", the Garey–Johnson notion; every polynomial is bounded by some ℓ^k + k
--   - reading: "strongly co-NP-hard, even when there are only two agent types" → two clauses, each with its own k: the bounded problem over all instances and over instances with numTypes v ≤ 2; reason: "even when" asserts hardness of the problem and of the restricted problem; "only two" read as at most two (one type always admits an MMS allocation, p.3)
--   - encoding: the restricted problem (instances outside the class are excluded) → a language whose non-members include the codes of instances outside the class; reason: membership in the class is decidable in polynomial time and the class contains no-instances, so reductions to the restricted problem and to this language convert into each other
-- source:
--   Gupta, Seetharaman, The Existence of Maximin Share Allocations is Δ₂ᴾ-complete, arXiv:2609.15841 (held version, sha256 a43b06b9…), Theorem 1.3, p.43 (PDF p.45); also p.4 (PDF p.6); 'strongly', p.3 (PDF p.5)

import Mathlib
import Definitions.Def_MMSDelta2_Supplement_NPHard
import Definitions.Def_MMSDelta2_Supplement_numTypes
import Definitions.Def_MMSDelta2_Supplement_IntBounded
import Definitions.Def_MMSDelta2_Supplement_GoodsLangOn

namespace MMSDelta2.Supplement

/-- **Theorem 1.3**, p.43 (PDF p.45); also stated on p.4 (PDF p.6).

S. Gupta, S. Seetharaman, *The Existence of Maximin Share Allocations is Δ₂ᴾ-complete*,
arXiv:2609.15841 (held version, sha256 a43b06b9…).

"Deciding whether an additive goods instance admits an MMS allocation is strongly co-NP-hard, even
when there are only two agent types."

**Formalization Note.** "Strongly" (p.3: "the hardness persists even when all numerical values are
given in unary") is the Garey–Johnson notion: for some polynomial `ℓ ↦ ℓ^k + k`, the problem
restricted to instances whose values are integers of absolute value at most that polynomial of the
instance's code length (`IntBounded k`) is co-NP-hard. Two clauses, each with its own polynomial:
the problem over all instances, and over instances with at most two agent types
(`numTypes v ≤ 2`). The number of agents is unrestricted. -/
theorem theorem_1_3 :
    (∃ k : ℕ, CoNPHard (GoodsLangOn (IntBounded k))) ∧
      (∃ k : ℕ, CoNPHard (GoodsLangOn (fun n m v => IntBounded k n m v ∧ numTypes v ≤ 2))) := by sorry

end MMSDelta2.Supplement
