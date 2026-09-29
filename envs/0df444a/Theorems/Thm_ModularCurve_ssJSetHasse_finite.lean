-- Prove2me | Theorems.Thm_ModularCurve_ssJSetHasse_finite
-- name    : ModularCurve.ssJSetHasse_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/09062ddb-d68c-5afc-9327-283729a3a91a
-- title:
--   Finiteness of the Hasse-supersingular j-invariants
-- statement:
--   Let $q$ be a prime with $q \neq 2$, and let $K$ be an algebraically closed field of characteristic $q$. Consider the subset $\mathrm{ssJSetHasse}\,q\,K$ of $K$ consisting of those $j$ such that for every Weierstrass curve $W$ over $K$ which is elliptic (non-vanishing discriminant, so that its $j$-invariant is defined) and satisfies $W.j = j$, the Hasse invariant of $W$ vanishes; here the Hasse invariant of $W$ is the coefficient of $X^{q-1}$ in the $((q-1)/2)$-th power of the polynomial attached to the two-torsion cubic $4X^3 + b_2X^2 + 2b_4X + b_6$ of $W$. The assertion is that this subset of $K$ is finite. Note that only finiteness is asserted: no bound on its cardinality, and no identification of it with the set of $j$-invariants of supersingular elliptic curves, is part of the conclusion.
--
--   This is the finiteness half of the classical statement that, in characteristic $q$, only finitely many $j$-invariants are supersingular (as detected by the vanishing of the Hasse invariant). It is used in the construction of $p$-fibre data for the Hecke-algebra level rings, via [`ModularCurve.HpoolLevelRing.exists_pFibre_dictionary`](thm.html#ModularCurve.HpoolLevelRing.exists_pFibre_dictionary).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ssJSetHasse_finite.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_Polynomial_DeuringPolynomial
import Definitions.Def_ModularCurve_LegendreJ

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial ModularCurve

theorem ModularCurve.ssJSetHasse_finite (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) (K : Type*) [Field K]
    [IsAlgClosed K] [CharP K q] :
    (ssJSetHasse q K).Finite := by sorry
