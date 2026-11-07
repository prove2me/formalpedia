-- Prove2me | Theorems.Thm_NoPerfectRandComp_lemma_5_11
-- name    : NoPerfectRandComp.lemma_5_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:44:56.42073+00:00
-- url     : https://prove2.me/theorems/6cca0d2b-dea0-452d-917c-33b6743a693c
-- title:
--   Lemma 5.11 — robust AND–OR evaluation at error $\varepsilon/(1-4\varepsilon)$ with $9m^2B$ queries
-- statement:
--   Let $m \ge 1$ and $0 \le \varepsilon \le 1/8$. Suppose each entry $e$ of an $m\times m$ array has an independent randomized oracle, using fresh randomness on each call and at most $B$ queries, whose error is at most $\varepsilon$ on a promised entry and whose output distribution is unrestricted on other entries. Then the partial short-circuit AND–OR rule can be evaluated with error at most
--   $$
--   \frac{\varepsilon}{1 - 4\varepsilon}
--   $$
--   using at most $9m^2B$ queries on every input.
--
--   It preserves the small error of the seed algorithm through the core, so that no amplification is needed in the upper bound (29).
--
--   **Formalization Note** Entry $e$'s oracle is a randomized query algorithm on the block of entry $e$, making at most $B$ queries on every block; a promised entry is one whose block lies in the domain of its partial function.
--
--   Differences from the source:
--   - reading: "an independent randomized oracle" for each entry, "using at most B queries" → a randomized query algorithm on the entry's block with at most B queries on every block, the evaluator being a randomized query algorithm on the whole array; reason: the lemma is a query-complexity statement and is applied (p.26) to seed algorithms on blocks; fresh randomness per call is what running a distribution over trees gives
--   - encoding: ε ≤ 1/8 → 0 ≤ ε ≤ 1/8 (real ε); reason: ε bounds an error probability; for ε < 0 the error hypothesis forces every entry's domain to be empty, so the AND–OR domain is empty (m ≥ 1) and nothing is excluded
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), Lemma 5.11, p.25

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_NoPerfectRandComp_andOr

namespace NoPerfectRandComp

/-- Lemma 5.11 of Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), pp.25–26 (robust evaluation at small error): let `m ≥ 1` and suppose
each entry of an `m × m` array has an independent randomized oracle, using fresh randomness on each
call and at most `B` queries, with error at most `ε ≤ 1/8` on a promised entry and unrestricted
output distribution on other entries. Then the partial short-circuit AND–OR rule can be evaluated
with error at most `ε/(1 − 4ε)` using at most `9 m² B` queries on every input.

**Formalization Note** Entry `e`'s oracle is a randomized query algorithm `A e` on block `e`
(at most `B` queries on every block); "promised" means the block lies in the domain of the
entry's partial function `h e`. The evaluator is a randomized query algorithm on the whole array
making at most `9 m² B` queries on every input. -/
theorem lemma_5_11 (m : ℕ) (hm : 1 ≤ m) {κ : Type} (h : Fin m × Fin m → PartialFn κ) (B : ℕ)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 8)
    (A : Fin m × Fin m → QAlgorithms.RandDecisionTree κ Bool Bool)
    (hAB : ∀ e, QAlgorithms.RandMakesAtMost (A e) B)
    (hAε : ∀ e, ∀ y ∈ (h e).dom, QAlgorithms.successProb (A e) y (!(h e).val y) ≤ ε) :
    ∃ A' : QAlgorithms.RandDecisionTree (Fin m × Fin m × κ) Bool Bool,
      QAlgorithms.RandMakesAtMost A' (9 * m ^ 2 * B) ∧
      ∀ x ∈ (andOr m h).dom,
        QAlgorithms.successProb A' x (!(andOr m h).val x) ≤ ε / (1 - 4 * ε) := by sorry

end NoPerfectRandComp
