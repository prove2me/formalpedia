-- Prove2me | Theorems.Thm_OffloadGNEP_Ext_theorem_2
-- name    : OffloadGNEP.Ext.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:41:16.520441+00:00
-- url     : https://prove2.me/theorems/6805f9a3-3ddc-468c-b0d7-2aa8d1d58644
-- title:
--   Theorem 2 — variational solutions and equilibria of the extended game
-- statement:
--   Under Assumption A and the standing conditions on the cloudlet server count and offloadable fraction, two assertions hold.
--
--   1. If the load $L(x)$ is less than one throughout $\prod_u\widetilde K_u$, a profile $\bar x$ solves the original game's VI on $K$ if and only if some nonnegative price $\bar\rho$ makes $(\bar x,\bar\rho)$ a Nash equilibrium of the extended game:
--
--      $$\bar x\in\operatorname{SOL}(K,F)\quad\Longleftrightarrow\quad\exists\bar\rho,\; (\bar x,\bar\rho)\in\operatorname{NE}_{\mathrm{ext}}.$$
--
--   2. If $F$ is monotone on $\prod_u\widetilde K_u$, then $F_e$ is monotone on $K_e$.
--
--   The result identifies a price that converts the coupled equilibrium problem into an ordinary Nash game and transfers monotonicity to its VI formulation.
--
--   **Formalization Note** The load bound repairs a pole that can make the first assertion false; it is weaker than the paper's condition (18). The second assertion reads “original game is monotone” on the $x$-part of $K_e$. Monotonicity merely on $K$ does not control $F_e$ at the additional profiles in $K_e$.
-- source:
--   Cardellini et al., A game-theoretic approach to computation offloading in mobile cloud computing, accepted manuscript (IRIS Sapienza 11573/779661; DOI 10.1007/s10107-015-0881-6), p. 15, Theorem 2; p. 16, proof

import Mathlib
import Definitions.Def_OffloadGNEP_Ext_Setting

namespace OffloadGNEP.Ext

/-- Theorem 2, p. 15, with the two domain repairs recorded in the mission notes. -/
theorem theorem_2 {N : ℕ} (P : Params N)
    (hA : P.AssumptionA) (hS : P.Standing) :
    ((∀ x ∈ Kprod P, load P x < 1) →
      ∀ xb, IsVISol (K P) (F P) xb ↔ ∃ ρb, IsExtNE P xb ρb) ∧
    (IsMonotoneOn (Kprod P) (F P) → IsMonotoneOnE (Ke P) (Fe P)) := by sorry

end OffloadGNEP.Ext
