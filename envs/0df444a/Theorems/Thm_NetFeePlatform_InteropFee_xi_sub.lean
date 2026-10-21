-- Prove2me | Theorems.Thm_NetFeePlatform_InteropFee_xi_sub
-- name    : NetFeePlatform.InteropFee.xi_sub
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T10:13:17.155842+00:00
-- url     : https://prove2.me/theorems/e3c0a45c-927f-4fca-9e29-58a749464f28
-- title:
--   Proof of Proposition 7, p. 52 — ξ(t; λ̄) = ξ(t; λ̲) − γ(λ̄ − λ̲)(J − 1 − φʲ)nʲ, and J − 1 − φʲ > 0 except in duopoly without outside option
-- statement:
--   Let $J \ge 2$ and $w \ge 0$. For any two interoperability levels $\underline\lambda$, $\overline\lambda$ and every net fee $\tau$, with $n = n(\tau)$ and $\varphi = \varphi(\tau)$ the symmetric share and diversion ratio:
--
--   1. the difference identity
--   $$\xi(\tau;\overline\lambda) = \xi(\tau;\underline\lambda) - \gamma(\overline\lambda - \underline\lambda)(J - 1 - \varphi)\,n;$$
--   2. if $J \ge 3$ or $w > 0$, then $J - 1 - \varphi > 0$;
--   3. if $J = 2$ and $w = 0$ (duopoly without an outside option), then $\varphi = 1$ and $J - 1 - \varphi = 0$.
--
--   Hence a higher interoperability level lowers $\xi$ everywhere when $\gamma > 0$, except in duopoly without an outside option, where $\xi$ does not depend on $\lambda$.
--
--   **Formalization Note** The paper's case distinction "unless $J = 2$ and $\varphi^j = 1$" is stated through the primitives: under Logit, $\varphi = 1$ at a symmetric profile with $J = 2$ exactly when $w = 0$.
-- source:
--   Ekmekci, White & Wu, Platform Competition and Interoperability: The Net Fee Model, accepted working-paper version (December 12, 2024), p. 52, Appendix E.2, proof of Proposition 7

import Mathlib
import Definitions.Def_NetFeePlatform_Competition_Setting
import Definitions.Def_NetFeePlatform_InteropFee_Symmetric

namespace NetFeePlatform.InteropFee
theorem xi_sub {J : ℕ} (hJ : 2 ≤ J) (w c γ lamLo lamHi τ : ℝ) (hw : 0 ≤ w) :
    xi w c γ lamHi J τ
        = xi w c γ lamLo J τ - γ * (lamHi - lamLo) * ((J : ℝ) - 1 - phiSym w J τ) * nSym w J τ ∧
      ((3 ≤ J ∨ 0 < w) → 0 < (J : ℝ) - 1 - phiSym w J τ) ∧
      (J = 2 → w = 0 → (J : ℝ) - 1 - phiSym w J τ = 0) := by sorry
end NetFeePlatform.InteropFee
