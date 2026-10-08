-- Prove2me | Theorems.Thm_OffloadGNEP_Ext_isExtNE_iff_isVISolE
-- name    : OffloadGNEP.Ext.isExtNE_iff_isVISolE
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:41:57.066984+00:00
-- url     : https://prove2.me/theorems/a4e512ad-d5ad-48d4-af4b-ca2fd14dc849
-- title:
--   Extended-game Nash equilibria equal VI solutions
-- statement:
--   Let the offloading parameters satisfy Assumption A and the standing server and offloading conditions. Suppose the cloudlet load is strictly below one at every profile in the product of the private feasible sets. Then a profile $\bar x$ and price $\bar\rho$ form a Nash equilibrium of the extended game exactly when they solve its variational inequality:
--
--   $$ (\bar x,\bar\rho)\in\operatorname{NE}_{\mathrm{ext}}\quad\Longleftrightarrow\quad(\bar x,\bar\rho)\in\operatorname{SOL}(K_e,F_e). $$
--
--   This equivalence lets the extended game be studied through its VI map.
--
--   **Formalization Note** The load bound is an explicit repair: the users' cost has a pole on a private feasible set if the bound is omitted.
-- source:
--   Cardellini et al., A game-theoretic approach to computation offloading in mobile cloud computing, accepted manuscript (IRIS Sapienza 11573/779661; DOI 10.1007/s10107-015-0881-6), p. 15, extended-game equivalence, citing [17, Proposition 1.4.2]

import Mathlib
import Definitions.Def_OffloadGNEP_Ext_Setting

namespace OffloadGNEP.Ext

/-- The extended Nash game is VI(F_e,K_e), as stated on p. 15. -/
theorem isExtNE_iff_isVISolE {N : ℕ} (P : Params N)
    (hA : P.AssumptionA) (hS : P.Standing)
    (hD : ∀ x ∈ Kprod P, load P x < 1)
    (xb : Fin N → OffloadGNEP.Exist.Tier → ℝ) (ρb : ℝ) :
    IsExtNE P xb ρb ↔ IsVISolE (Ke P) (Fe P) (xb, ρb) := by sorry

end OffloadGNEP.Ext
