-- Prove2me | Theorems.Thm_LinSysAmp_lemma_4_5_accept
-- name    : LinSysAmp.lemma_4_5_accept
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:59:22.507192+00:00
-- url     : https://prove2.me/theorems/eb68aa43-b900-4341-a6eb-c393464cf9ba
-- title:
--   Lemma 4.5, item 2 — $1-e_k>1/4$
-- statement:
--   Let $1\le k\le n$. The probability $e_k$ that an invertible update of rank $k$ outputs $\bot$ does not depend on $M$, and
--   $$
--   1-e_k>\frac14.
--   $$
--
--   The bound holds for every finite field, including $\mathbb F_2$, and is uniform in $n$ and $k$. It is why rejected updates cost only a constant factor in the number of attempts.
--
--   Differences from the source:
--   - encoding: "e_k does not depend on M" → e_k has no M argument; reason: the definition samples U, V alone, so the clause holds by construction
-- source:
--   Couteau, Melissaris, Radhika Sajith, Hardness Self-Amplification in Linear Algebra and Fine-Grained Cryptography, arXiv:2611.04680 (version held, sha256 af7a90ac…), Lemma 4.5, item 2, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_LinSysAmp_rankUpdate

set_option autoImplicit false

namespace LinSysAmp

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Lemma 4.5, item 2, p.19 (PDF p.21). Couteau, Melissaris, Radhika Sajith, arXiv:2611.04680
(version held, sha256 af7a90ac…).

"The probability e_k does not depend on M, and 1 − e_k > 1/4."

**Formalization Note.** `e_k = ek n k F` is defined from `U, V` alone (Definition 4.4), so "does not
depend on M" holds by construction. The bound is stated for every finite field (`q = 2` included) and
every `1 ≤ k ≤ n`. -/
theorem lemma_4_5_accept {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    (1 : ℝ) / 4 < 1 - ek n k F := by sorry

end LinSysAmp
