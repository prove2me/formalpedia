-- Prove2me | Theorems.Thm_NetFeePlatform_InteropDominance_zeta_sub
-- name    : NetFeePlatform.InteropDominance.zeta_sub
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T10:13:05.095334+00:00
-- url     : https://prove2.me/theorems/628b1321-f490-4004-8308-b6509053cd8f
-- title:
--   Appendix E.2, proof of Proposition 6, p. 52 — ζ(n; λ̲) − ζ(n; λ̄) = 2γ(λ̲ − λ̄)(2n − 1) < 0 for n > 1/2 (corrected value)
-- statement:
--   Let $\gamma>0$, let $\underline\lambda<\overline\lambda$ be two levels of interoperability, and let $n>1/2$. Then
--
--   $$\zeta(n;\underline\lambda)-\zeta(n;\overline\lambda)=2\gamma(\underline\lambda-\overline\lambda)(2n-1)<0.$$
--
--   In the proof of Proposition 6 this is applied at the dominant share $n=\overline n^1$ of an equilibrium under $\overline\lambda$, where $\zeta(\overline n^1;\overline\lambda)=0$, and shows $\zeta(\overline n^1;\underline\lambda)<0$.
--
--   **Formalization Note** The paper prints the difference as $4(\underline\lambda-\overline\lambda)\gamma\overline n^1$; the correct value, from the definition of $\zeta$, is $2\gamma(\underline\lambda-\overline\lambda)(2\overline n^1-1)$. Both are negative under the stated hypotheses, so the argument is unaffected. The Lean states the correct value and the sign.
-- source:
--   Ekmekci, White & Wu, Platform Competition and Interoperability: The Net Fee Model, accepted working-paper version (December 12, 2024), p. 52, Appendix E.2, proof of Proposition 6

import Mathlib
import Definitions.Def_NetFeePlatform_Competition_Setting
import Definitions.Def_NetFeePlatform_InteropDominance_Zeta

namespace NetFeePlatform.InteropDominance

theorem zeta_sub (γ lamLo lamHi n : ℝ) (hγ : 0 < γ) (hlt : lamLo < lamHi) (hn : 1 / 2 < n) :
    zeta γ lamLo n - zeta γ lamHi n = 2 * γ * (lamLo - lamHi) * (2 * n - 1) ∧
    zeta γ lamLo n - zeta γ lamHi n < 0 := by sorry

end NetFeePlatform.InteropDominance
