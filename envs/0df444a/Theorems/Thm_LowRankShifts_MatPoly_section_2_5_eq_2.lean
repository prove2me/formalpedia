-- Prove2me | Theorems.Thm_LowRankShifts_MatPoly_section_2_5_eq_2
-- name    : LowRankShifts.MatPoly.section_2_5_eq_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:57:21.571425+00:00
-- url     : https://prove2.me/theorems/69b13c01-f6b7-47b1-8505-a7342cd6e3d5
-- title:
--   §2.5, Eq. (2) — the variance of a real function on F_p^{n×m} through its nonzero Fourier coefficients
-- statement:
--   Let $p$ be a prime. For every real-valued $q:\mathbb F_p^{n\times m}\to\mathbb R$,
--
--   $$\operatorname*{Var}_{A\sim\mathbb F_p^{n\times m}}[q(A)]\;=\;p^{-2nm}\sum_{W\neq 0}|\hat q(W)|^2 ,$$
--
--   where $A$ is uniform, the variance is $\mathbb E[(q-\mathbb E q)^2]$, and $\hat q$ is the Fourier transform of `LowRankShifts_MatPoly_Fourier`.
--
--   It follows from Parseval's identity and $\hat q(0)=\sum_X q(X)$; the proof of Lemma 3.2 uses it to bound the variance of a smoothed function.
--
--   **Formalization Note.** The variance is `unifVar` (population variance under the uniform law) from `ZamirInversion581_Mult_Uniform`; $|\cdot|$ is the complex norm.
--
--   Differences from the source:
--   - encoding: Var_{A∼F_p^{n×m}}[q(A)] → `unifVar q`, the mean of (q − mean q)² under the uniform law; reason: the variance of q(A) for uniform A
--   - encoding: ω_p^{−⟨W,X⟩} with ω_p = e^{2πi/p} → `omegaInvPow (frob W X) = exp(−2πi·(frob W X).val/p)`; reason: the canonical representative in {0, …, p−1}; the same complex number
-- source:
--   Golovnev, Nagargoje, Shinkar, Singh, Stephens-Davidowitz, Worst-Case to Average-Case Reductions for Linear Algebra: Optimal, Simple, and General, STOC 2027 submission (manuscript sha256 ebcf9677…), p. 15 (PDF 18), §2.5, Eq. (2)

import Mathlib
import Definitions.Def_ZamirInversion581_Mult_Uniform
import Definitions.Def_LowRankShifts_MatPoly_Fourier

set_option autoImplicit false

namespace LowRankShifts.MatPoly

/-- §2.5, Eq. (2) (p. 15): for any real-valued `q : F_p^{n×m} → ℝ`,
`Var_{A ∼ F_p^{n×m}}[q(A)] = p^{−2nm} Σ_{W ≠ 0} |q̂(W)|²`. -/
theorem section_2_5_eq_2 {p : ℕ} [Fact p.Prime] {n m : ℕ}
    (q : Matrix (Fin n) (Fin m) (ZMod p) → ℝ) :
    ZamirInversion581.Mult.unifVar q =
      ((p : ℝ) ^ (2 * n * m))⁻¹ *
        ∑ W ∈ Finset.univ.filter (fun W : Matrix (Fin n) (Fin m) (ZMod p) => W ≠ 0),
          ‖fourier (fun X => (q X : ℂ)) W‖ ^ 2 := by sorry

end LowRankShifts.MatPoly
