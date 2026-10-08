-- Prove2me | Theorems.Thm_OffloadGNEP_Ext_isVISol_K_iff_multiplier
-- name    : OffloadGNEP.Ext.isVISol_K_iff_multiplier
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:41:46.907277+00:00
-- url     : https://prove2.me/theorems/832c3b5b-30f7-4a6e-a8e3-1cc108fb3727
-- title:
--   The shared cloudlet constraint has a VI multiplier
-- statement:
--   For a candidate profile $\bar x$, consider the VI over $K=(\prod_u\widetilde K_u)\cap\Omega$. It has a solution at $\bar x$ exactly when $\bar x$ satisfies the shared utilization cap and there is a nonnegative scalar $\bar\rho$ such that
--
--   $$\bar\rho\bigl(L(\bar x)-U_{\max}\bigr)=0,\qquad \bar x\in\operatorname{SOL}\bigl(\textstyle\prod_u\widetilde K_u,\,F+\operatorname{price}(\bar\rho)\bigr).$$
--
--   Thus one multiplier accounts for the shared affine constraint while the individual feasible sets remain in the VI domain.
--
--   **Formalization Note** Assumption A is the standing hypothesis of Section 5; it keeps the response-time denominators positive on $K$. The standing condition $n>0$ makes the coefficient $\delta_u/n$ the paper's load coefficient. The equivalence concerns the VI and does not assume convexity of the users' cost functions.
-- source:
--   Cardellini et al., A game-theoretic approach to computation offloading in mobile cloud computing, accepted manuscript (IRIS Sapienza 11573/779661; DOI 10.1007/s10107-015-0881-6), pp. 15–16, Lagrange multiplier of (11) and proof of Theorem 2

import Mathlib
import Definitions.Def_OffloadGNEP_Ext_Setting

namespace OffloadGNEP.Ext

/-- The shared affine constraint admits one multiplier in the VI KKT conditions. -/
theorem isVISol_K_iff_multiplier {N : ℕ} (P : Params N)
    (hA : P.AssumptionA) (hS : P.Standing)
    (xb : Fin N → OffloadGNEP.Exist.Tier → ℝ) :
    IsVISol (K P) (F P) xb ↔
      xb ∈ Omega P ∧ ∃ ρb : ℝ, 0 ≤ ρb ∧
        ρb * (load P xb - P.Umax) = 0 ∧
        IsVISol (Kprod P) (fun x => F P x + price P ρb) xb := by sorry

end OffloadGNEP.Ext
