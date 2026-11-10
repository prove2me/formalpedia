-- Prove2me | Theorems.Thm_HarmonicCalib_Principal_lemma_3_2
-- name    : HarmonicCalib.Principal.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:05:49.847264+00:00
-- url     : https://prove2.me/theorems/581aa067-c541-462a-bf72-489c0fa10842
-- title:
--   Lemma 3.2 — finite Hilbert matrix moment bounds $\|K_T x\|_q \le Cq\|x\|_q$ for $q = 2^k$
-- statement:
--   There is an absolute constant $C > 0$ such that for every $T \ge 1$, every $q = 2^k$ with integer $k \ge 1$ and every $x \in \mathbb R^T$,
--   $$\|K_T x\|_q \le C q \|x\|_q \quad\text{and}\quad \|K_T^{\mathsf T} x\|_q \le C q \|x\|_q,$$
--   where $(K_T)_{ts} = 1/(2(t-s)-1)$ and $\|x\|_q = (\sum_{t<T} |x_t|^q)^{1/q}$.
--
--   Differences from the source:
--   - generalization: ‖K_T x‖_q ≤ Cq‖x‖_q (the displayed statement (12)) → the same bound for K_T and for its transpose K_Tᵀ, with one C; reason: the source asserts after the proof that the same bounds hold for K_Tᵀ (p. 13) and uses them for K_Tᵀ in Lemma 3.3 (pp. 14–15); the Lean statement implies (12)
--   - encoding: an absolute constant C → ∃ C : ℝ, 0 < C ∧ …; reason: any admissible C is positive (x = e_0 gives |(K_T x)_0| = 1), so requiring 0 < C excludes nothing
--   - encoding: q = 2^k, ‖x‖_q → lqNorm ((2:ℝ)^k) with real rpow exponents; reason: the same number
-- source:
--   Fishelson and Mohri (2026), High-Dimensional Online Calibration from Harmonic Weights, arXiv:2610.07740 (version dated October 29, 2026; PDF SHA256 62ac31a3…), Lemma 3.2, p. 12 (= Lemma 1.3, p. 5); transpose: p. 13

import Mathlib
import Definitions.Def_HarmonicCalib_Principal_Hilbert

namespace HarmonicCalib.Principal

/-- Lemma 3.2 (finite Hilbert matrix moment bounds, p. 12): one absolute constant `C` such that for
every `T ≥ 1`, every `q = 2^k` with integer `k ≥ 1` and every `x ∈ ℝ^T`,
`‖K_T x‖_q ≤ C q ‖x‖_q`; the same bound for the transpose `K_Tᵀ` (asserted on pp. 13–14). -/
theorem lemma_3_2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℕ), 1 ≤ T → ∀ (k : ℕ), 1 ≤ k → ∀ x : Fin T → ℝ,
      lqNorm ((2 : ℝ) ^ k) (Matrix.mulVec (hilbertK T) x) ≤ C * (2 : ℝ) ^ k * lqNorm ((2 : ℝ) ^ k) x ∧
      lqNorm ((2 : ℝ) ^ k) (Matrix.mulVec (hilbertK T).transpose x) ≤
        C * (2 : ℝ) ^ k * lqNorm ((2 : ℝ) ^ k) x := by sorry

end HarmonicCalib.Principal
