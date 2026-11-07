-- Prove2me | Theorems.Thm_LDPSelect_list_minimal
-- name    : LDPSelect.list_minimal
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:56:08.844081+00:00
-- url     : https://prove2.me/theorems/185d93a7-90fc-4ac3-a3d2-cb5b5edca658
-- title:
--   A.7, minimality of the list — every $O_i$ and $B_m$ is minor-minimal, and the $B_m$ are incomparable
-- statement:
--   1. Each $O_i$, $i=1,\dots,9$, is outside $\mathcal G$, and every proper minor of $O_i$ is in $\mathcal G$.
--   2. For every $m\ge4$, $B_m$ is outside $\mathcal G$ and every proper minor of $B_m$ is in $\mathcal G$.
--   3. Distinct $B_m$ are incomparable: for $m,m'\ge4$, if $B_m$ is a minor of $B_{m'}$ then $m=m'$.
--
--   Differences from the source:
--   - encoding: minors by repeated contraction and deletion, up to isomorphism → one contraction of a feasible set followed by one deletion, with an injective relabelling; reason: the paper's own reduction (§3.4, p.8): (F∖D)/I = (F/I)∖D
--   - encoding: a proper minor → a minor on fewer elements; reason: a minor on as many elements is the family itself up to isomorphism
--   - reading: distinct B_m are incomparable → for m, m′ ≥ 4, B_m a minor of B_{m′} forces m = m′; reason: the list has m ≥ 4; B_1 is a minor of every B_{m′}, so the statement is about the listed B_m
-- source:
--   Chen, Wang, When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy, STOC 2027 submission (manuscript sha256 2e2d6157…), A.7, Minimality of the list, p.20 (pdf p.21)

import Mathlib
import Definitions.Def_LDPSelect_InClass
import Definitions.Def_LDPSelect_IsMinorOf
import Definitions.Def_LDPSelect_Obstructions

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LDPSelect

/-- Chen, Wang, *When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy*, STOC 2027 submission (manuscript sha256 2e2d6157…), A.7, p.20, Minimality of the list.

Each listed family lies outside `G`, all its proper minors lie in `G`, and distinct `B_m` are
incomparable.

**Formalization Note.** Incomparability is stated for `m, m' ≥ 4`, the `B_m` of the list; `B_1` is a
minor of every `B_m'`. -/
theorem list_minimal :
    (∀ i : Fin 9, ¬ InClass (O i) ∧
      ∀ (k : ℕ) (Q : Family k), k < 4 → IsMinorOf Q (O i) → InClass Q) ∧
    (∀ m, 4 ≤ m → ¬ InClass (B m) ∧
      ∀ (k : ℕ) (Q : Family k), k < m + 1 → IsMinorOf Q (B m) → InClass Q) ∧
    (∀ m m', 4 ≤ m → 4 ≤ m' → IsMinorOf (B m) (B m') → m = m') := by sorry

end LDPSelect
