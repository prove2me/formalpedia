-- Prove2me | Theorems.Thm_InfoDerivQT_dim_composite
-- name    : InfoDerivQT.dim_composite
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-02T13:44:33.989986+00:00
-- url     : https://prove2.me/theorems/667570c5-f4b5-4dd6-b742-623dee46f3b8
-- title:
--   Corollary 15 — informational dimension is multiplicative, $d_{AB}=d_Ad_B$
-- statement:
--   Let $T$ satisfy the six principles and $A,B$ systems. If $A$, $B$ and $AB$ have maximal sets of perfectly distinguishable pure states of sizes $N$, $M$ and $K$ respectively, then
--
--   $$K=N\,M,$$
--
--   that is, $d_{AB}=d_A\,d_B$.
-- source:
--   G. Chiribella, G. M. D'Ariano, P. Perinotti, *Informational derivation of quantum theory*, Phys. Rev. A 84, 012311 (2011), https://doi.org/10.1103/PhysRevA.84.012311 (arXiv:1011.6451), p. 012311-16, Sec. VII, Corollary 15

import Mathlib
import Definitions.Def_InfoDerivQT_principles

namespace InfoDerivQT
theorem dim_composite (T : OPT) (hT : T.SatisfiesPrinciples) (A B : T.Sys)
    {N M K : ℕ} (φ : Fin N → Vec (T.size A)) (ψ : Fin M → Vec (T.size B))
    (Φ : Fin K → Vec (T.size (T.comp A B)))
    (hφ : T.IsMaximalPerfDistPure A φ) (hψ : T.IsMaximalPerfDistPure B ψ)
    (hΦ : T.IsMaximalPerfDistPure (T.comp A B) Φ) :
    K = N * M := by sorry
end InfoDerivQT
