-- Prove2me | Theorems.Thm_MasulloRH_raw_real_kernel_residue
-- name    : MasulloRH.raw_real_kernel_residue
-- status  : Proved
-- author  : @phi9t
-- created : 2026-11-21T01:54:23.10604+00:00
-- url     : https://prove2.me/theorems/e593c194-b57f-4644-973c-fac730f4cf1d
-- title:
--   Leading endpoint coefficient of the unsubtracted power kernel
-- statement:
--   Let $p\in\mathbb C$ be any fixed exponent, and for real $t>0$ put $t^p=\exp(p\log t)$. The unsubtracted real-place kernel has the following leading coefficient at its lower endpoint:
--   $$
--   \lim_{t\downarrow1}(t-1)t^p\frac{\sqrt t}{t^2-1}=\frac12.
--   $$
--
--   The result isolates the local singular behavior of the power kernel used in the endpoint audit of the Masullo trace reconstruction, with no restriction on $\operatorname{Re}p$. It is a statement about a one-sided limit. It does not by itself formalize divergence of an improper integral, any uniform cutoff estimate, a trace formula, or the Riemann hypothesis. This auxiliary endpoint calculation was derived independently.
-- source:
--   Independent auxiliary endpoint calculation developed for the Prove2Me Masullo mission, not a numbered theorem claimed from the manuscript. Context: public definition MasulloRH_RegularizedTrace (regularizedArch), https://prove2.me/api/v1/definitions/bcb9a5ab-1b4b-473b-86a1-cd5bc2827c5a, explicitly a reconstruction of Masullo §§1.4.2–1.4.5, pp.28–30. Analytic ingredients: Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474, Complex.hasStrictDerivAt_cpow_const in https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Pow/Deriv.lean and HasDerivAt.tendsto_slope in Mathlib/Analysis/Calculus/Deriv/Slope.lean.

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.Convert
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring.RingNF

set_option autoImplicit false
open Filter Set
open scoped Topology

theorem MasulloRH.raw_real_kernel_residue (p : ℂ) :
    Tendsto
      (fun t : ℝ => ((t - 1 : ℝ) : ℂ) *
        ((t : ℂ) ^ p * ((Real.sqrt t / (t ^ 2 - 1) : ℝ) : ℂ)))
      (𝓝[>] (1 : ℝ)) (𝓝 (1 / 2 : ℂ)) := by sorry
