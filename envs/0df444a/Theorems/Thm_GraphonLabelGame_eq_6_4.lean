-- Prove2me | Theorems.Thm_GraphonLabelGame_eq_6_4
-- name    : GraphonLabelGame.eq_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:22:29.659685+00:00
-- url     : https://prove2.me/theorems/3b891550-a93c-4442-b698-6b51f58f7d2b
-- title:
--   (6.4) — strong operator convergence bounds the edge densities: $\frac1{n^2}\sum_{ij}\xi^n_{ij}=\|W_{\xi^n}\|_{L^1}\le\bar A$
-- statement:
--   Let $W\in L^1_+[0,1]^2$ and let $\xi^n$ be $n\times n$ matrices with nonnegative entries and zero diagonal such that the step kernels $W_{\xi^n}$ converge to $W$ in the strong operator topology. Then there exists $\bar A>0$ such that
--   $$\frac1{n^2}\sum_{i,j=1}^n\xi^n_{ij}=\|W_{\xi^n}\|_{L^1[0,1]^2}\le\bar A\qquad\text{for all }n.$$
--
--   Both the identity and the uniform bound are part of the claim. The bound is the uniform control of total masses used repeatedly in the proof of Theorem 6.1.
--
--   Differences from the source:
--   - generalization: ∀ n ∈ ℕ (ℕ = {1, 2, …}) → ∀ n : ℕ, including n = 0; reason: at n = 0 both sides are 0, so the statement specializes to the printed one
--   - encoding: ‖W_ξ‖_{L¹[0,1]²} → ∫_{[0,1]²} |W_ξ(u,v)| d(u,v); reason: definition (2.2)
--   - reading: "an arbitrary n×n matrix ξⁿ with positive entries and zeros on the diagonal" (§3.4, p.10) → IsInteractionMatrix: ξⁿᵢⱼ ≥ 0 and ξⁿᵢᵢ = 0; reason: positive entries contradict a zero diagonal; §3.1 (p.7) says nonnegative entries
-- source:
--   Lacker, Soret, A Label-State Formulation of Stochastic Graphon Games and Approximate Equilibria on Large Networks, arXiv:2204.09642v1, proof of Theorem 6.1, (6.4), p.25

import Mathlib
import Definitions.Def_GraphonLabelGame_Kernel

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace GraphonLabelGame

/-- **(6.4)**. Lacker–Soret, arXiv:2204.09642v1, proof of Theorem 6.1, (6.4), p.25.
Let `W ∈ L¹₊[0, 1]²` and let `ξⁿ` be `n × n` matrices with nonnegative entries and zero diagonal
whose step kernels converge to `W` in the strong operator topology. Then there exists
`Ā > 0` such that `(1/n²) Σᵢⱼ ξⁿᵢⱼ = ‖W_{ξⁿ}‖_{L¹[0,1]²} ≤ Ā` for all `n`. -/
theorem eq_6_4 (W : ℝ → ℝ → ℝ) (hW : IsKernelL1Plus W)
    (ξ : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ) (hξ : ∀ n, IsInteractionMatrix (ξ n))
    (hSOT : SOTConv (fun n => stepKernel (ξ n)) W) :
    ∃ Abar : ℝ, 0 < Abar ∧ ∀ n : ℕ,
      (1 / (n : ℝ) ^ 2) * ∑ i, ∑ j, ξ n i j =
          ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, |stepKernel (ξ n) p.1 p.2| ∧
        ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, |stepKernel (ξ n) p.1 p.2| ≤ Abar := by sorry

end GraphonLabelGame
