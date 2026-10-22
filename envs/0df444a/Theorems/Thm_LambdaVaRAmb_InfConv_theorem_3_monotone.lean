-- Prove2me | Theorems.Thm_LambdaVaRAmb_InfConv_theorem_3_monotone
-- name    : LambdaVaRAmb.InfConv.theorem_3_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:29:47.891509+00:00
-- url     : https://prove2.me/theorems/f94dc4ae-ef98-4c0b-9b5f-ca294f0bb740
-- title:
--   Theorem 3, monotonicity — 𝒜̃ₓ is increasing (decreasing) when every 𝒜⁽ⁱ⁾ₓ is
-- statement:
--   Let $n\ge1$ and let $\{\mathcal A^{(i)}_x\}_{x\in\mathbb R}$, $i\in[n]$, be families of downsets, with $\widetilde{\mathcal A}_x=\bigcup_{y_1+\dots+y_n=x}\{\bigcup_iA_i:A_i\in\mathcal A^{(i)}_{y_i}\}$.
--
--   1. If every family $\{\mathcal A^{(i)}_x\}$ is increasing, then $\{\widetilde{\mathcal A}_x\}$ is increasing.
--   2. If every family $\{\mathcal A^{(i)}_x\}$ is decreasing, then $\{\widetilde{\mathcal A}_x\}$ is decreasing.
--
--   Together with Theorem 1, the first part shows that the inf-convolution of risk measures of the form $\Lambda\mathrm{VaR}^w$ with increasing $\Lambda$ is again of that form.
--
--   **Formalization Note** The paper also asserts that $\{\widetilde{\mathcal A}_x\}$ is left-continuous in the decreasing case. That claim is false under the printed hypotheses (two Lebesgue capacities on $[0,1]$ with $\Lambda_1$ right- but not left-continuous give a counterexample) and is not posed. $n\ge1$ is implicit in the paper; for $n=0$ the family is not monotone.
-- source:
--   Liu and Schied, Lambda Value-at-Risk under ambiguity and risk sharing, arXiv:2511.00717v1, p. 15, Theorem 3, last sentence

import Mathlib
import Definitions.Def_LambdaVaRAmb_InfConv_Setting

namespace LambdaVaRAmb.InfConv

theorem theorem_3_monotone {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (𝒜 : Fin n → ℝ → Set (Set Ω)) (h𝒜 : ∀ i x, IsDownset (𝒜 i x)) :
    ((∀ i, Monotone (𝒜 i)) → Monotone (convFamily 𝒜)) ∧
      ((∀ i, Antitone (𝒜 i)) → Antitone (convFamily 𝒜)) := by sorry

end LambdaVaRAmb.InfConv
