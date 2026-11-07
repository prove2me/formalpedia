-- Prove2me | Theorems.Thm_NoPerfectRandComp_lemma_5_3
-- name    : NoPerfectRandComp.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:48:23.759278+00:00
-- url     : https://prove2.me/theorems/90488237-7f31-45f9-aed4-1b5e0e4cd301
-- title:
--   Lemma 5.3 — weak evaluation of $\hat M_q$ with success $\ge\frac12+\frac1{10q}$
-- statement:
--   For odd $q \ge 3$ there is a randomized algorithm $E_q$ using at most $(6q+2)\hat C_q$ queries such that
--   $$
--   \Pr[E_q(x) = \hat M_q(x)] \ \ge\ \frac12 + \frac1{10q} \qquad \text{for every input } x .
--   $$
--
--   Its signed bias is at least $1/(5q)$ everywhere at cost $O(b_q q)$, which gives the upper bound on $\mathrm{LR}(\hat M_q)$ and the weak evaluations of Lemma 5.10.
--
--   Differences from the source:
--   - generalization: the paper's fixed pointer-cell encoding → every admissible encoding; reason: the proof only runs the detector of Lemma 5.2, which holds for every admissible encoding
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), Lemma 5.3, pp.19–20

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_NoPerfectRandComp_Mhat

namespace NoPerfectRandComp

/-- Lemma 5.3 of Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), pp.19–20 (weak evaluation of the total inner function): for odd `q ≥ 3`,
an algorithm `E_q` using at most `(6q + 2) Ĉ_q` queries satisfies
`Pr[E_q(x) = M̂_q(x)] ≥ 1/2 + 1/(10q)` for every input `x`.

**Formalization Note** Stated for every admissible encoding; the query bound holds on every
input. -/
theorem lemma_5_3 (q : ℕ) (hq : Odd q) (hq3 : 3 ≤ q) (enc : Encoding (bq q) (PtrCell q)) :
    ∃ E : QAlgorithms.RandDecisionTree (Fin q × (Fin q × Fin q × Fin (Chat q))) Bool Bool,
      QAlgorithms.RandMakesAtMost E ((6 * q + 2) * Chat q) ∧
      ∀ x, 1 / 2 + 1 / (10 * (q : ℝ)) ≤ QAlgorithms.successProb E x (Mhat q enc x) := by sorry

end NoPerfectRandComp
