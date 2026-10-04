-- Prove2me | Theorems.Thm_InfoDerivQT_size_eq_dim_sq
-- name    : InfoDerivQT.size_eq_dim_sq
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-02T15:20:56.799012+00:00
-- url     : https://prove2.me/theorems/68cd0cac-09e7-4a6d-9cf0-f160e2960e47
-- title:
--   Theorem 12 — dimension of the state space, $D_A=d_A^2$
-- statement:
--   Let $T$ satisfy the six principles and $A$ a system. If $\{\varphi_i\}_{i=1}^N$ is a maximal set of perfectly distinguishable pure states of $A$, then the dimension of the real vector space spanned by the states is
--
--   $$D_A=N^2=d_A^2.$$
--
--   This is the relation between the size of the state space and the number of perfectly distinguishable states that Hardy took as an axiom.
-- source:
--   G. Chiribella, G. M. D'Ariano, P. Perinotti, *Informational derivation of quantum theory*, Phys. Rev. A 84, 012311 (2011), https://doi.org/10.1103/PhysRevA.84.012311 (arXiv:1011.6451), p. 012311-21, Sec. IX, Theorem 12 (Dimension of the state space)

import Mathlib
import Definitions.Def_InfoDerivQT_principles

namespace InfoDerivQT
theorem size_eq_dim_sq (T : OPT) (hT : T.SatisfiesPrinciples) (A : T.Sys)
    {N : ℕ} (φ : Fin N → Vec (T.size A)) (hφ : T.IsMaximalPerfDistPure A φ) :
    T.size A = N ^ 2 := by sorry
end InfoDerivQT
