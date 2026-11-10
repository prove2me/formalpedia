-- Prove2me | Theorems.Thm_HarmonicCalib_Principal_lemma_3_2_q2
-- name    : HarmonicCalib.Principal.lemma_3_2_q2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:05:43.788201+00:00
-- url     : https://prove2.me/theorems/c9b5100d-535f-4b54-a9ae-02782b2a0610
-- title:
--   Lemma 3.2, $q=2$ case — $\|K_T x\|_2 \le (\pi/2)\|x\|_2$ (proof of Lemma 3.2)
-- statement:
--   For every $T \ge 1$ and every $x \in \mathbb R^T$,
--   $$\|K_T x\|_2 \le \frac{\pi}{2}\|x\|_2 \quad\text{and}\quad \|K_T^{\mathsf T} x\|_2 \le \frac{\pi}{2}\|x\|_2 .$$
--   This is the first step of the proof of Lemma 3.2 (p. 12) and supplies the explicit constant $\pi/2$ used for $\gamma(B_2^d, B_2^d) \le \pi/2$ in Lemma 3.3.
--
--   Differences from the source:
--   - generalization: ‖K_T x‖₂ ≤ (π/2)‖x‖₂ (p. 12) → the same bound for K_T and for K_Tᵀ; reason: the source states that the q = 2 bound also holds for K_Tᵀ and uses it in that form (p. 14); the Lean statement implies the p. 12 claim
--   - encoding: ‖·‖₂ → lqNorm 2 (rpow exponents 2 and 1/2); reason: the same number
-- source:
--   Fishelson and Mohri (2026), High-Dimensional Online Calibration from Harmonic Weights, arXiv:2610.07740 (version dated October 29, 2026; PDF SHA256 62ac31a3…), proof of Lemma 3.2, p. 12; transpose: pp. 13–14

import Mathlib
import Definitions.Def_HarmonicCalib_Principal_Hilbert

namespace HarmonicCalib.Principal

/-- The `q = 2` case of Lemma 3.2 with its explicit constant (proof of Lemma 3.2, p. 12):
`‖K_T x‖_2 ≤ (π/2) ‖x‖_2` for every `T ≥ 1` and `x ∈ ℝ^T`, and the same for `K_Tᵀ`
(used for `K_Tᵀ` on p. 14). -/
theorem lemma_3_2_q2 :
    ∀ (T : ℕ), 1 ≤ T → ∀ x : Fin T → ℝ,
      lqNorm 2 (Matrix.mulVec (hilbertK T) x) ≤ Real.pi / 2 * lqNorm 2 x ∧
      lqNorm 2 (Matrix.mulVec (hilbertK T).transpose x) ≤ Real.pi / 2 * lqNorm 2 x := by sorry

end HarmonicCalib.Principal
