-- Prove2me | Theorems.Thm_GenStieltjes_ExactOrder_theorem_A1_mem
-- name    : GenStieltjes.ExactOrder.theorem_A1_mem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:46:00.408478+00:00
-- url     : https://prove2.me/theorems/a1d834ac-e8eb-472e-9c62-65cead8c3b79
-- title:
--   Theorem A1, first part — $\mu\in\mathcal M_\alpha\Rightarrow I^+_\eta\mu\in\mathcal M_{\alpha+\eta}$
-- statement:
--   Let $\alpha>0$, $\eta>0$, and let $\mu$ be a measure on $[0,\infty)$ with
--   $$\int_{[0,\infty)}\frac{\mu(dt)}{(1+t)^\alpha}<\infty .$$
--   Then its left-sided Riemann–Liouville fractional integral $\nu=I^+_\eta\mu$ (Definition A1) satisfies
--   $$\int_{[0,\infty)}\frac{\nu(dt)}{(1+t)^{\alpha+\eta}}<\infty,$$
--   that is, $I^+_\eta$ maps $\mathcal M_\alpha$ into $\mathcal M_{\alpha+\eta}$.
--
--   This is the integrability half of Theorem A1; in the proof of Theorem 16 it shows that a non-decreasing $\Phi$ yields a measure in $\mathcal M_{\beta-\varepsilon}$.
--
--   **Formalization Note** Measures live on `ℝ≥0`; the paper's clause $\mu(\{\infty\})=\nu(\{\infty\})$ concerns the atom at infinity, which has no counterpart here.
-- source:
--   Karp & Prilepkina, Generalized Stieltjes transforms: basic aspects, arXiv:1111.4271v2, p. 16, Theorem A1 (first part); Definition A1, p. 15

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P11
import Definitions.Def_GenStieltjes_ExactOrder_Basic

namespace GenStieltjes.ExactOrder

open MeasureTheory
open scoped NNReal ENNReal
open QAlgorithms.Papers.Independent.Renew46.P11 (PositiveReal StieltjesRepresentation StieltjesClass)

/-- Theorem A1, first part, p. 16: if `μ ∈ M_α` and `η > 0` then `I^+_η μ ∈ M_{α+η}`. -/
theorem theorem_A1_mem (α η : ℝ) (hα : 0 < α) (hη : 0 < η) (μ : Measure ℝ≥0)
    (hμ : InM α μ) :
    InM (α + η) (rlIntegral η μ) := by sorry

end GenStieltjes.ExactOrder
