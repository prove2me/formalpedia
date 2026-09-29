-- Prove2me | Theorems.Thm_IsLocalRing_hensel_lift_unique
-- name    : IsLocalRing.hensel_lift_unique
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/7f8986d9-1158-51f3-9fb0-45beaa0c1c35
-- title:
--   Uniqueness of Hensel lifts in a local ring
-- statement:
--   Let $R$ be a commutative local ring, $f \in R[X]$ a polynomial over $R$, and $a, b \in R$. Assume that $a$ is a root of $f$ and that $b$ is a root of $f$ (that is, $f$ evaluated at each of $a$ and $b$ vanishes), that the difference $b - a$ lies in the maximal ideal of $R$, and that the value $f'(a)$ of the formal derivative of $f$ at $a$ is a unit of $R$. Then $a = b$. Thus a root of $f$ at which $f'$ is invertible is the only root of $f$ in its residue class modulo the maximal ideal; no completeness or separatedness hypothesis on $R$ is needed, only that $R$ be local.
--
--   This is the uniqueness half of Hensel's lemma, separated from the existence statement: simple roots are rigid modulo the maximal ideal, in any local ring. It is used in the treatment of places of an algebraic curve, where it identifies a root of a polynomial over a local ring with the value predicted by a Taylor coefficient expansion, via [`AlgebraicCurve.Place.eq_map_mk_taylorCoeff_of_evalEval_C_add_X_eq_zero`](thm.html#AlgebraicCurve.Place.eq_map_mk_taylorCoeff_of_evalEval_C_add_X_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_hensel_lift_unique.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_DedekindDomain_AdicValuation_InlineSpecific
import Definitions.Def_AlgebraicCurve_PlaceCompletion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial IsLocalRing in

theorem IsLocalRing.hensel_lift_unique {R : Type*} [CommRing R] [IsLocalRing R] {f : Polynomial R} {a b : R}
    (ha : f.IsRoot a) (hb : f.IsRoot b) (hmem : b - a ∈ IsLocalRing.maximalIdeal R)
    (hunit : IsUnit (f.derivative.eval a)) : a = b := by sorry
