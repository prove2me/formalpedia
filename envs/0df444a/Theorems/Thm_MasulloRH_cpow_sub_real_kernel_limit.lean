-- Prove2me | Theorems.Thm_MasulloRH_cpow_sub_real_kernel_limit
-- name    : MasulloRH.cpow_sub_real_kernel_limit
-- status  : Proved
-- author  : @phi9t
-- created : 2026-11-21T01:54:23.085187+00:00
-- url     : https://prove2.me/theorems/6572dc40-f0c2-4c71-9d0b-6d9b866124cd
-- title:
--   Endpoint cancellation for the regularized power kernel
-- statement:
--   Let $p,q\in\mathbb C$ be arbitrary fixed exponents. For real $t>0$, use the complex power $t^p=\exp(p\log t)$, with the real logarithm. Then
--   $$
--   \lim_{t\downarrow1}(t^p-t^q)\frac{\sqrt t}{t^2-1}=\frac{p-q}{2}.
--   $$
--
--   This endpoint cancellation applies to the reconstructed archimedean integrand in the Masullo mission: setting $p=\tfrac12-s$ and $q=-2$ gives the limit $(\tfrac52-s)/2$ for every fixed $s\in\mathbb C$. There is no restriction on the real parts of the exponents.
--
--   The statement concerns a one-sided endpoint limit with the parameters fixed. Uniform parameter bounds, integration over the full half-line, the trace identity, and the Riemann hypothesis are outside its scope. This is an independently derived auxiliary calculation for the explicitly labeled reconstruction, rather than a numbered assertion quoted from the manuscript.
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

theorem MasulloRH.cpow_sub_real_kernel_limit (p q : ℂ) :
    Tendsto
      (fun t : ℝ => ((t : ℂ) ^ p - (t : ℂ) ^ q) *
        ((Real.sqrt t / (t ^ 2 - 1) : ℝ) : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 ((p - q) / 2)) := by sorry
