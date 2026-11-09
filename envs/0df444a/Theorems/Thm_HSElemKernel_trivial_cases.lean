-- Prove2me | Theorems.Thm_HSElemKernel_trivial_cases
-- name    : HSElemKernel.trivial_cases
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:24:42.756988+00:00
-- url     : https://prove2.me/theorems/ed691f79-cbf4-4a55-bf03-23fe1f4dd3a3
-- title:
--   Section 2.1 — the trivial cases of $d$-Hitting Set
-- statement:
--   For every Hitting Set instance $(U, \mathcal S, k)$:
--
--   1. if $\emptyset \in \mathcal S$, the instance is a NO-instance;
--   2. if $\mathcal S = \emptyset$, it is a YES-instance;
--   3. if $k = 0$ and $\mathcal S \ne \emptyset$, it is a NO-instance;
--   4. if $\emptyset \notin \mathcal S$ and $k \ge |U|$, it is a YES-instance (the set $U$ is a hitting set);
--   5. if $k = 1$, it is a YES-instance if and only if $\mathcal S = \emptyset$ or the input sets have a common element.
--
--   After these cases the kernel may assume $\emptyset \notin \mathcal S$, $\mathcal S \ne \emptyset$ and $2 \le k < |U|$, the standing assumptions of the randomized encoding.
--
--   Differences from the source:
--   - reading: For k = 1, "we check whether the input sets have a common element" → k = 1 → (YES ↔ S = ∅ ∨ some element lies in every input set); reason: this is what the check decides; the disjunct S = ∅ keeps it true when U = ∅, a case the page has already handled
-- source:
--   Sheng–Xiao, A Near-Linear Element-Kernel for d-Hitting Set, arXiv:2609.06512 (held version, sha256 aca9c70e…), Section 2.1, trivial cases, p.3

import Mathlib
import Definitions.Def_HSElemKernel_IsYes

namespace HSElemKernel

/-- **Section 2.1, trivial cases** (Sheng–Xiao, *A Near-Linear Element-Kernel for d-Hitting Set*, arXiv:2609.06512 (held version, sha256 aca9c70e…), Section 2.1, p.3): for every Hitting Set instance
`(U, S, k)`,
1. if `∅ ∈ S`, it is a NO-instance;
2. if `S = ∅`, it is a YES-instance;
3. if `k = 0` and `S ≠ ∅`, it is a NO-instance;
4. if `∅ ∉ S` and `k ≥ |U|`, it is a YES-instance;
5. if `k = 1`, it is a YES-instance iff `S = ∅` or the input sets have a common element.

**Formalization Note** Clause 5 is what the page's test "we check whether the input sets have a
common element" decides; the disjunct `S = ∅` keeps it true when `U = ∅`. -/
theorem trivial_cases (I : HSInstance) :
    (∅ ∈ I.S → ¬ IsYes I) ∧ (I.S = ∅ → IsYes I) ∧ (I.k = 0 → I.S ≠ ∅ → ¬ IsYes I) ∧
      (∅ ∉ I.S → I.n ≤ I.k → IsYes I) ∧
      (I.k = 1 → (IsYes I ↔ I.S = ∅ ∨ ∃ u : Fin I.n, ∀ A ∈ I.S, u ∈ A)) := by sorry

end HSElemKernel
