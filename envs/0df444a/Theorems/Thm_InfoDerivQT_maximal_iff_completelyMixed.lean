-- Prove2me | Theorems.Thm_InfoDerivQT_maximal_iff_completelyMixed
-- name    : InfoDerivQT.maximal_iff_completelyMixed
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-02T10:07:02.051438+00:00
-- url     : https://prove2.me/theorems/0acdb292-138f-4ab4-966e-72d9dc740d85
-- title:
--   Theorem 6 — a perfectly distinguishable set is maximal iff its uniform mixture is completely mixed
-- statement:
--   Let $T$ be an operational-probabilistic theory satisfying the six principles, $A$ a system, $N\ge 1$, and let $\rho_1,\dots,\rho_N\in\mathrm{St}_1(A)$ be perfectly distinguishable. Then the family is maximal (no normalized state $\rho_{N+1}$ can be added keeping it perfectly distinguishable) if and only if
--
--   $$\omega=\frac1N\sum_{i=1}^N\rho_i$$
--
--   is completely mixed.
--
--   This links the combinatorial notion of maximal distinguishable sets to the convex-geometric notion of completely mixed states, and is used to define the informational dimension.
-- source:
--   G. Chiribella, G. M. D'Ariano, P. Perinotti, *Informational derivation of quantum theory*, Phys. Rev. A 84, 012311 (2011), https://doi.org/10.1103/PhysRevA.84.012311 (arXiv:1011.6451), p. 012311-14, Sec. V, Theorem 6 (with Definitions 1, 5, 6)

import Mathlib
import Definitions.Def_InfoDerivQT_principles

namespace InfoDerivQT
theorem maximal_iff_completelyMixed (T : OPT) (hT : T.SatisfiesPrinciples) (A : T.Sys)
    {N : ℕ} (hN : 0 < N) (ρ : Fin N → Vec (T.size A))
    (hρ : T.PerfectlyDistinguishable A ρ) :
    T.IsMaximalPerfDist A ρ ↔ T.IsCompletelyMixed A ((1 / (N : ℝ)) • ∑ i, ρ i) := by sorry
end InfoDerivQT
