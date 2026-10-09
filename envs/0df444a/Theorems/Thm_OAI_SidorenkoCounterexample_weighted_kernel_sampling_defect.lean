-- Prove2me | Theorems.Thm_OAI_SidorenkoCounterexample_weighted_kernel_sampling_defect
-- name    : OAI.SidorenkoCounterexample.weighted_kernel_sampling_defect
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-08T15:14:25.258538+00:00
-- url     : https://prove2.me/theorems/812e557e-4900-43b3-a139-a0bbfa382dfd
-- title:
--   Finite host sampling with the 595/n collision error
-- statement:
--   Let $W$ be any symmetric $[0,1]$-valued kernel on a finite probability space. Write $\mu$ for its edge mean and $\tau$ for its homomorphism moment for the fixed incidence pattern $H$. For every integer $n>0$, there is a finite probability distribution on simple graphs $G$ with vertex set $\mathrm{Fin}(n)$ such that
--
--   $$
--   \mathbb E\big[t(H,G)-t(K_2,G)^{66}\big]
--   \le \tau+\frac{595}{n}-\left(\left(1-\frac1n\right)\mu\right)^{66}.
--   $$
--
--   The distribution is represented by finitely many graphs and nonnegative weights of total mass one. The homomorphism density counts all vertex maps, including noninjective maps. The term $595/n$ is the collision bound $\binom{35}{2}/n$; the factor $1-1/n$ accounts for the omission of graph loops. The statement applies without a strict kernel gap and isolates the quantitative sampling step from the counterexample's kernel construction.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/RandomHost.lean, lemmas expectedEdgeDensity and expectedHomDensity_bound, combined with Symmetrization.lean, FiniteLaw.mean_pow_le (Jensen). This is their finite-distribution expected-defect formulation.

import Mathlib
import Definitions.Def_SidorenkoWeightedKernelData

open scoped BigOperators
open OAI.SidorenkoCounterexample

theorem OAI.SidorenkoCounterexample.weighted_kernel_sampling_defect
    (K : WeightedKernelData) (n : ℕ) (hn : 0 < n) :
    ∃ m : ℕ, ∃ w : Fin m → ℝ,
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
      ∃ G : Fin m → SimpleGraph (Fin n),
        (∑ i, w i * (homDensity H (G i) - (edgeDensity (G i)) ^ 66)) ≤
          kernelPatternMoment K + 595 / (n : ℝ) -
            ((1 - 1 / (n : ℝ)) * kernelEdgeMean K) ^ 66 := by sorry
