-- Prove2me | Theorems.Thm_LaurentSeries_commute_heckeU_heckeU
-- name    : LaurentSeries.commute_heckeU_heckeU
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/da358160-9e7b-5077-ac0d-7d901831f176
-- title:
--   Commutativity of Uₐ and U_b on Laurent series
-- statement:
--   Let $R$ be a commutative ring and let $a, b$ be natural numbers with $0 < a$ and $0 < b$. For a positive natural number $\ell$, the operator `heckeU R` $\ell$ is the $R$-linear endomorphism of `LaurentSeries R` (Hahn series over $R$ indexed by $\mathbb{Z}$ with support bounded below) sending $f$ to the Laurent series whose $n$-th coefficient is the $(\ell n)$-th coefficient of $f$, the support of this new coefficient function being bounded below because that of $f$ is and $\ell > 0$. The theorem asserts that `heckeU R a ha` and `heckeU R b hb` commute in the endomorphism ring of `LaurentSeries R`, i.e. that their product in either order is the same $R$-linear map, which is the composite $f \mapsto \bigl(n \mapsto f_{abn}\bigr)$. In $q$-expansion notation, $U_a U_b = U_b U_a$ on $R((q))$, both being $U_{ab}$; no hypothesis beyond positivity of $a$ and $b$ is required, and no modularity or level structure enters.
--
--   This is the elementary commutation relation among the formal $U$-operators acting on $q$-expansions, the Laurent-series analogue of the relation $U_aU_b = U_{ab}$ for Atkin–Lehner $U$-operators. It is used in the project's formal Hecke-operator calculus: it feeds the corresponding commutation statements for the $T$-operators and for $U$ against $T$, and ultimately a rank bound for a quotient of a Hecke torsion module by the kernel of reduction modulo $\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LaurentSeries_commute_heckeU_heckeU.lean

import Mathlib
import Definitions.Def_LaurentSeries_HeckeU
import Definitions.Def_LaurentSeries_HeckeV
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open ModularCurve LaurentSeries

theorem LaurentSeries.commute_heckeU_heckeU (R : Type*) [CommRing R] (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Commute (heckeU R a ha) (heckeU R b hb) := by sorry
