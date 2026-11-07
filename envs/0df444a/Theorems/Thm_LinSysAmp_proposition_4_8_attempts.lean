-- Prove2me | Theorems.Thm_LinSysAmp_proposition_4_8_attempts
-- name    : LinSysAmp.proposition_4_8_attempts
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:00:56.624824+00:00
-- url     : https://prove2.me/theorems/4fed526f-cbaf-42d6-b793-82ed5ca73785
-- title:
--   Proof of Proposition 4.8 — an attempt succeeds with probability $(1-e_k)\,(K_kh)(M)$, independently of $y$ and of the other attempts
-- statement:
--   Let $1\le k\le n$, let $\mathcal O$ be any oracle, let $h$ be its success function and let $g=K_kh$. For every invertible $M$, every $y$ and every number of attempts $t$, the algorithm of Figure 3 outputs the correct solution with probability exactly
--   $$
--   \Pr\bigl[\mathcal B_k(M,y)=M^{-1}y\bigr]=1-\bigl(1-(1-e_k)\,g(M)\bigr)^t,
--   $$
--   and every output in its support is either $\bot$ or $M^{-1}y$.
--
--   The right side does not depend on $y$, which is how the final guarantee reaches every right-hand side at once. The second clause is the "never wrong" property of Figure 3.
--
--   Differences from the source:
--   - generalization: stated for the oracle of Proposition 4.8, which solves LINEQ with probability ≥ α → any oracle, with no success hypothesis; reason: the page's argument does not use the hypothesis; the printed case is a special case
--   - encoding: each attempt succeeds with probability (1 − e_k)·g(M), "independently of y and of the other attempts" → the closed form 1 − (1 − (1 − e_k) g(M))^t for t attempts; reason: the closed form is what independence and a y-free rate mean for the attempt loop
-- source:
--   Couteau, Melissaris, Radhika Sajith, Hardness Self-Amplification in Linear Algebra and Fine-Grained Cryptography, arXiv:2611.04680 (version held, sha256 af7a90ac…), proof of Proposition 4.8, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_LinSysAmp_MarkovNotions
import Definitions.Def_LinSysAmp_figure3

set_option autoImplicit false

open Matrix

namespace LinSysAmp

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Proof of Proposition 4.8, per-attempt success probability (p.22, PDF p.24). Couteau, Melissaris,
Radhika Sajith, arXiv:2611.04680 (version held, sha256 af7a90ac…).

"For a fixed R ≠ ⊥, the right-hand side R(y + Mz) = Ry + RMz is uniform, since RM is invertible.
Hence, an attempt succeeds with probability (1 − e_k)·g(M), where g(M) = E_R[h(RM)] = (K_k h)(M),
independently of y and of the other attempts." Together with "if the check passes, then
w − z = M⁻¹y, and B_k never outputs a wrong solution".

**Formalization Note.** `h` is `succFn O` and `g = K_k h` is `applyK (Kk n k F) (succFn O)`.
"Independently of y and of the other attempts" is the closed form: after `t` attempts of Figure 3
(`figure3`), the probability of output `M⁻¹y` is `1 − (1 − (1 − e_k) g(M))^t`, whose right side does
not involve `y`. The second conjunct: every output of Figure 3 is `⊥` or `M⁻¹y`, for every oracle. -/
theorem proposition_4_8_attempts {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (O : Oracle n F) (t : ℕ)
    (M : InvMat n F) (y : Fin n → F) :
    (figure3 O k t M.1 y (some (M.1⁻¹ *ᵥ y))).toReal =
        1 - (1 - (1 - ek n k F) * applyK (Kk n k F) (succFn O) M) ^ t ∧
      ∀ o ∈ (figure3 O k t M.1 y).support, o = none ∨ o = some (M.1⁻¹ *ᵥ y) := by sorry

end LinSysAmp
