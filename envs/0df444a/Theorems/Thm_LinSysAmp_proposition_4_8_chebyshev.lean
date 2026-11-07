-- Prove2me | Theorems.Thm_LinSysAmp_proposition_4_8_chebyshev
-- name    : LinSysAmp.proposition_4_8_chebyshev
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:59:41.074078+00:00
-- url     : https://prove2.me/theorems/886e2e1e-7fee-47c2-bed2-aeb6cd63c72d
-- title:
--   Proof of Proposition 4.8 — stationarity, the variance bound $16q^{-2k}\mu$ and Chebyshev
-- statement:
--   Let $1\le k\le n$ and let $h:\mathrm{GL}_n(F)\to[0,1]$ have mean $\mu=\mathbb E_M[h(M)]$ over uniform $M$. Put $g=K_kh$ and $q=|F|$. Then $\mathbb E_M[g(M)]=\mu$,
--   $$
--   \mathbb E_M\bigl[(g(M)-\mu)^2\bigr]\le16\,q^{-2k}\mu,
--   $$
--   and, if $\mu>0$,
--   $$
--   \Pr_M\bigl[g(M)<\mu/2\bigr]\le\frac{64\,q^{-2k}}{\mu}.
--   $$
--
--   This is the step that makes the success rate after one update nearly the same from almost every starting matrix, and it is where the exceptional fraction of the main theorem comes from.
--
--   Differences from the source:
--   - generalization: h is the success function of the oracle → any h with 0 ≤ h ≤ 1; reason: the page's argument uses only 0 ≤ h ≤ 1; the success function is a special case
--   - encoding: the display ends "≤ 64q^{−2k}/α" → the bound 64q^{−2k}/µ under 0 < µ; reason: the last inequality is µ ≥ α, available only for the oracle, and it is used in `proposition_4_8_figure3`
--   - encoding: the intermediate chain ‖K_k(h − µ)‖² ≤ λ_k²µ(1 − µ) → the endpoints of the chain; reason: the intermediate terms are steps of the proof
-- source:
--   Couteau, Melissaris, Radhika Sajith, Hardness Self-Amplification in Linear Algebra and Fine-Grained Cryptography, arXiv:2611.04680 (version held, sha256 af7a90ac…), proof of Proposition 4.8, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_LinSysAmp_MarkovNotions
import Definitions.Def_LinSysAmp_rankUpdate

set_option autoImplicit false

open Matrix

namespace LinSysAmp

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Proof of Proposition 4.8, stationarity, variance bound and Chebyshev step (p.22, PDF p.24).
Couteau, Melissaris, Radhika Sajith, arXiv:2611.04680 (version held, sha256 af7a90ac…).

"Since the uniform distribution on GL_n(F_q) is stationary for K_k, we have E_M[g(M)] = µ. […] Hence
E_M[(g(M) − µ)²] = ‖K_k(h − µ)‖² ≤ λ_k² µ(1 − µ) ≤ 16q^{−2k}µ. By the Chebyshev inequality,
Pr_M[g(M) < µ/2] ≤ 16q^{−2k}µ/(µ/2)² = 64q^{−2k}/µ."

**Formalization Note.** Stated for every `h : GL_n(F) → [0, 1]` (the paper's `h` is the oracle's
success function; the argument uses only `0 ≤ h ≤ 1`), with `µ = E_M[h(M)]` over `M` uniform in
`GL_n(F) = InvMat n F` and `g = K_k h = applyK (Kk n k F) h`. Probabilities over `M` are normalized
counts. The Chebyshev conclusion assumes `µ > 0`, where the printed division by `µ` is defined. The
final "≤ 64q^{−2k}/α" of the paper is `µ ≥ α` and is left to the final step. -/
theorem proposition_4_8_chebyshev {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (h : InvMat n F → ℝ)
    (h0 : ∀ M, 0 ≤ h M) (h1 : ∀ M, h M ≤ 1) :
    let mu : ℝ := (Fintype.card (InvMat n F) : ℝ)⁻¹ * ∑ M, h M
    (Fintype.card (InvMat n F) : ℝ)⁻¹ * ∑ M, applyK (Kk n k F) h M = mu ∧
      (Fintype.card (InvMat n F) : ℝ)⁻¹ * ∑ M, (applyK (Kk n k F) h M - mu) ^ 2 ≤
        16 * ((Fintype.card F : ℝ) ^ (2 * k))⁻¹ * mu ∧
      (0 < mu →
        ((Finset.univ.filter fun M => applyK (Kk n k F) h M < mu / 2).card : ℝ) /
            (Fintype.card (InvMat n F) : ℝ) ≤
          64 * ((Fintype.card F : ℝ) ^ (2 * k))⁻¹ / mu) := by sorry

end LinSysAmp
