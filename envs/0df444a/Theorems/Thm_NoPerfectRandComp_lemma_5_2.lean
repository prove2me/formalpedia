-- Prove2me | Theorems.Thm_NoPerfectRandComp_lemma_5_2
-- name    : NoPerfectRandComp.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:46:46.100436+00:00
-- url     : https://prove2.me/theorems/001db4e5-5594-4491-8efc-fc9afabf55a7
-- title:
--   Lemma 5.2 — exact detector, $\Pr[D_q(x)=1]\in\{0,\rho_q\}$
-- statement:
--   Let $q$ be odd. There is a randomized algorithm $D_q$ using at most $(6q+2)\hat C_q$ bit queries such that, on every input $x$,
--   $$
--   \Pr[D_q(x) = 1] = \begin{cases} 0, & \hat g_q(x) = 0, \\ \rho_q := \dfrac{q-1}{2q}, & \hat g_q(x) = 1. \end{cases}
--   $$
--
--   Exactness of the acceptance probability on every one-input is what allows a uniformly correctly signed bias for the majority (Lemma 5.3).
--
--   **Formalization Note** The query bound holds on every input.
--
--   Differences from the source:
--   - generalization: q = 2^s − 1 (the standing choice of §5) → every odd q; reason: the proof uses only that q is odd (so that (q − 1)/2 is the number of good columns), and 2^s − 1 is odd
--   - generalization: the paper's fixed pointer-cell encoding → every admissible encoding; reason: the detector reads cells in full and uses only that the decoder is total
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), Lemma 5.2, p.19

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_NoPerfectRandComp_ghat

namespace NoPerfectRandComp

/-- Lemma 5.2 of Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), p.19 (exact detector): there is an algorithm `D_q` using at most
`(6q + 2) Ĉ_q` bit queries such that on every input `x`, `Pr[D_q(x) = 1] = 0` if `ĝ_q(x) = 0` and
`= ρ_q := (q − 1)/(2q)` if `ĝ_q(x) = 1`.

**Formalization Note** Stated for every odd `q` (the paper's `q = 2ˢ − 1`) and every admissible
encoding. The query bound holds on every input. -/
theorem lemma_5_2 (q : ℕ) (hq : Odd q) (enc : Encoding (bq q) (PtrCell q)) :
    ∃ D : QAlgorithms.RandDecisionTree (Fin q × Fin q × Fin (Chat q)) Bool Bool,
      QAlgorithms.RandMakesAtMost D ((6 * q + 2) * Chat q) ∧
      ∀ x, QAlgorithms.successProb D x true =
        if ghat q enc x then ((q : ℝ) - 1) / (2 * q) else 0 := by sorry

end NoPerfectRandComp
