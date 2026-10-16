-- Prove2me | Theorems.Thm_NewsBundling_Unilateral_prop1_qL_lt_qhat_lt_qH
-- name    : NewsBundling.Unilateral.prop1_qL_lt_qhat_lt_qH
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:07:02.915641+00:00
-- url     : https://prove2.me/theorems/9158d81d-1070-4021-962e-448efc135dda
-- title:
--   Proof of Proposition 1(ii), p. 31 — benchmark quality lies between candidates
-- statement:
--   Let $c>0$, $\phi_1<\beta$, and $0<\Lambda<1$. For the low-quality candidate $q_L=\phi_1/c$, benchmark quality $\hat q=\beta/c$, and high-quality candidate $q_H=(\beta-\Lambda\phi_1)/(c(1-\Lambda))$,
--
--   $$q_L<\hat q<q_H.$$
--
--   This comparison converts Lemma 4's quality regimes into the direction of the change from the no-bundling benchmark.
--
--   **Formalization Note** These four inequalities are the only parameter restrictions needed for this algebraic comparison, so this item does not carry the stronger Table 1 assumptions.
-- source:
--   de Cornière & Sarvary, Social Media and News: Content Bundling and News Quality, TSE Working Paper n° 1152 (August 2021), App. A, p. 31, proof of Proposition 1(ii), first sentence

import Mathlib
import Definitions.Def_NewsBundling_Unilateral_Setting

namespace NewsBundling.Unilateral

/-- Proof of Proposition 1(ii), p. 31: the benchmark quality lies between the candidates. -/
theorem prop1_qL_lt_qhat_lt_qH (β φ1 c Λ : ℝ)
    (hc : 0 < c) (hφ : φ1 < β) (hΛ0 : 0 < Λ) (hΛ1 : Λ < 1) :
    qL φ1 c < β / c ∧ β / c < qH β φ1 c Λ := by sorry

end NewsBundling.Unilateral
