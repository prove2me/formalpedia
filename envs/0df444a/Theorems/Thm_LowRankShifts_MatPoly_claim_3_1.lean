-- Prove2me | Theorems.Thm_LowRankShifts_MatPoly_claim_3_1
-- name    : LowRankShifts.MatPoly.claim_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:57:22.425197+00:00
-- url     : https://prove2.me/theorems/3cdacec7-ee68-4c52-810b-24cf14b76f95
-- title:
--   Claim 3.1 — the Fourier transform of the law of UVᵀ is p^{−r·rank W}
-- statement:
--   Let $p$ be a prime, $n,m,r\ge 0$, and let $\mu:\mathbb F_p^{n\times m}\to[0,1]$ be the law of $UV^T$ for independent uniform $U\in\mathbb F_p^{n\times r}$, $V\in\mathbb F_p^{m\times r}$:
--   $\mu(L)=\Pr_{U,V}[UV^T=L]$. Then for every $W\in\mathbb F_p^{n\times m}$
--
--   $$\hat\mu(W)=p^{-r\,\mathrm{rank}(W)},$$
--
--   and in particular $|\hat\mu(W)|\le p^{-r}$ for all $W\ne 0$.
--
--   This is the key estimate of the paper: shifting by a random rank-$r$ matrix damps every nonzero Fourier coefficient by $p^{-r}$, which is what Lemma 3.2 turns into concentration.
--
--   **Formalization Note.** $\mu$ is `lowRankLaw n m r`; $\mathrm{rank}$ is Mathlib's `Matrix.rank` over $\mathbb F_p$.
--
--   Differences from the source:
--   - encoding: µ(L) := Pr_{U∼F_p^{n×r}, V∼F_p^{m×r}}[UVᵀ = L] → `lowRankLaw n m r L`, the uniform probability over pairs (U, V); reason: independent uniform U and V are a uniform pair
--   - encoding: ω_p^{−⟨W,X⟩} with ω_p = e^{2πi/p} → `omegaInvPow (frob W X) = exp(−2πi·(frob W X).val/p)`; reason: the canonical representative in {0, …, p−1}; the same complex number
-- source:
--   Golovnev, Nagargoje, Shinkar, Singh, Stephens-Davidowitz, Worst-Case to Average-Case Reductions for Linear Algebra: Optimal, Simple, and General, STOC 2027 submission (manuscript sha256 ebcf9677…), p. 16 (PDF 19), Claim 3.1

import Mathlib
import Definitions.Def_LowRankShifts_MatPoly_Fourier

set_option autoImplicit false

namespace LowRankShifts.MatPoly

/-- Claim 3.1 (p. 16): for a prime `p` and `µ(L) := Pr_{U ∼ F_p^{n×r}, V ∼ F_p^{m×r}}[UVᵀ = L]`,
`µ̂(W) = p^{−r·rank(W)}` for every `W ∈ F_p^{n×m}`; in particular `|µ̂(W)| ≤ p^{−r}` for all
`W ≠ 0`. -/
theorem claim_3_1 {p : ℕ} [Fact p.Prime] (n m r : ℕ) :
    (∀ W : Matrix (Fin n) (Fin m) (ZMod p),
      fourier (fun L => (lowRankLaw n m r L : ℂ)) W = ((p : ℂ) ^ (r * W.rank))⁻¹) ∧
    (∀ W : Matrix (Fin n) (Fin m) (ZMod p), W ≠ 0 →
      ‖fourier (fun L => (lowRankLaw n m r L : ℂ)) W‖ ≤ ((p : ℝ) ^ r)⁻¹) := by sorry

end LowRankShifts.MatPoly
