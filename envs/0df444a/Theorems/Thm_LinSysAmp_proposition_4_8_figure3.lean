-- Prove2me | Theorems.Thm_LinSysAmp_proposition_4_8_figure3
-- name    : LinSysAmp.proposition_4_8_figure3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:01:07.403857+00:00
-- url     : https://prove2.me/theorems/20a82843-3149-407e-8ee5-1b37974add09
-- title:
--   Proof of Proposition 4.8, final paragraph — Figure 3 succeeds for all but a $64/(\alpha q^{2k})$ fraction of matrices
-- statement:
--   Let $1\le k\le n$, $\alpha>0$, $0<\delta<1/2$, and let $\mathcal O$ solve $\mathsf{LINEQ}_{n,q}$ with probability at least $\alpha$. With $t=\lceil8\alpha^{-1}\log(1/\delta)\rceil$, the algorithm of Figure 3 satisfies
--   $$
--   \Pr_{M\leftarrow\mathrm{GL}_n(F)}\Bigl[\forall y\in F^n:\ \Pr\bigl[\mathcal B_k(M,y)=M^{-1}y\bigr]\ge1-\delta\Bigr]\ge1-\frac{64}{\alpha q^{2k}}.
--   $$
--
--   Here $\log$ is the natural logarithm. This is the probabilistic content of the main theorem at the level of distributions, before the operation count and before the machine.
--
--   Differences from the source:
--   - encoding: the page's sentence bounds the failure probability for each M with g(M) ≥ µ/2 → the combined fraction bound, that is, this sentence together with the page's Chebyshev display; reason: the displayed conclusion of Proposition 4.8 for Figure 3; no other assumption
--   - encoding: Pr over M ← GL_n(F_q) → a normalized count over `InvMat n F`; reason: the uniform law on a finite set
-- source:
--   Couteau, Melissaris, Radhika Sajith, Hardness Self-Amplification in Linear Algebra and Fine-Grained Cryptography, arXiv:2611.04680 (version held, sha256 af7a90ac…), proof of Proposition 4.8, final paragraph, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_LinSysAmp_figure3

set_option autoImplicit false

open Matrix

namespace LinSysAmp

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Proof of Proposition 4.8, final paragraph, for Figure 3 (p.22, PDF p.24). Couteau, Melissaris,
Radhika Sajith, arXiv:2611.04680 (version held, sha256 af7a90ac…).

"Finally, let M be such that g(M) ≥ µ/2 ≥ α/2. Since 1 − e_k > 1/4, each attempt succeeds with
probability at least α/8, so all t attempts fail with probability at most (1 − α/8)^t ≤ exp(−αt/8) ≤ δ."
Combined with the Chebyshev step, this gives, for the algorithm of Figure 3 with
`t = ⌈8α⁻¹ log(1/δ)⌉`,
`Pr_{M←GL_n(F_q)}[∀y : Pr[B_k(M, y) = M⁻¹y] ≥ 1 − δ] ≥ 1 − 64/(αq^{2k})`.

**Formalization Note.** This is the probabilistic content of Proposition 4.8 for the distribution
`figure3` (no machine, no running time). `log` is the natural logarithm (§3.1) and `⌈·⌉` is
`Nat.ceil`. "Solves LINEQ with probability α" is `α ≤ lineqSuccess O`. The probability over `M` is a
normalized count over `InvMat n F`. -/
theorem proposition_4_8_figure3 {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (O : Oracle n F) (α δ : ℝ)
    (hα : 0 < α) (hαO : α ≤ lineqSuccess O) (hδ0 : 0 < δ) (hδ : δ < 1 / 2) :
    1 - 64 / (α * (Fintype.card F : ℝ) ^ (2 * k)) ≤
      ((Finset.univ.filter fun M : InvMat n F => ∀ y : Fin n → F,
          1 - δ ≤ (figure3 O k ⌈8 / α * Real.log (1 / δ)⌉₊ M.1 y (some (M.1⁻¹ *ᵥ y))).toReal).card : ℝ) /
        (Fintype.card (InvMat n F) : ℝ) := by sorry

end LinSysAmp
