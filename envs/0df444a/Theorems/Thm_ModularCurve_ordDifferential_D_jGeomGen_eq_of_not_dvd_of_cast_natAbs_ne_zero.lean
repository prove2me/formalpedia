-- Prove2me | Theorems.Thm_ModularCurve_ordDifferential_D_jGeomGen_eq_of_not_dvd_of_cast_natAbs_ne_zero
-- name    : ModularCurve.ordDifferential_D_jGeomGen_eq_of_not_dvd_of_cast_natAbs_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/910ff0f9-b9ad-5fcc-8011-df777e8845c7
-- title:
--   Order of d̄ j at affine places and tame cusps
-- statement:
--   Let $p\ge 5$ be a prime, let $N\ge 1$ with $p\nmid N$, and let $K$ be an algebraically closed field of characteristic $p$. Write $F=\mathrm{modularFunctionFieldC}\ K\ N$ for the subfield of the Laurent series field $K((q))$ generated over $K$ by the two series $\mathrm{jqModC}\ K=q^{-1}\cdot(\text{the }j\text{-numerator power series over }K)$ and its $q\mapsto q^N$ substitution $\mathrm{jqNModC}\ K\ N$, and let $\bar j=\mathrm{jGeomGen}\ K\ N$ be the first of these generators viewed in $F$. Assume that for every place $w$ of $F$ over $K$ (a proper valuation subring of $F$ containing $K$ whose ideals are principal) the element $d\pi_w\in\Omega_{F/K}$, for $\pi_w$ the chosen uniformizer, spans $\Omega_{F/K}$ over $F$, and that $\Omega_{F/K}\neq 0$. Then for every such place $w$ two statements hold. First, if both $\bar j$ and $\mathrm{jNGeomGen}\ K\ N$ lie in the valuation subring of $w$, then $\operatorname{ord}_w(d\bar j)=e_w-1$, where $\operatorname{ord}_w$ of a differential means the order of its coefficient with respect to $d\pi_w$, and $e_w$ is the non-negative truncation of $\operatorname{ord}_w\bigl(\bar j-\bar j(w)\bigr)$, $\bar j(w)\in K$ being the residue of $\bar j$ at $w$. Second, if $\operatorname{ord}_w\bar j<0$ and the image in $K$ of the natural number $|\operatorname{ord}_w\bar j|$ is nonzero, then $\operatorname{ord}_w(d\bar j)=\operatorname{ord}_w(\bar j)-1$.
--
--   This is the local computation of the divisor of $d\bar j$ on the modular curve of level $N$ in characteristic $p\ge 5$: at places lying over the affine $j$-line the order is one less than the ramification index over the $j$-line, and at a place where $\bar j$ has a pole of order prime to the characteristic the order is one less than that (negative) order. It feeds the canonical-divisor and Riemann–Roch computations for this function field, in particular [`ModularCurve.ordDifferential_D_jGeomGen_sub_weightFloor_eq`](thm.html#ModularCurve.ordDifferential_D_jGeomGen_sub_weightFloor_eq) and the Hecke-operator estimates [`ModularCurve.SSHeckeV2.ord_heckeMultiplier_eq_and_width_eq_and_mem_ssPlaces_of_mem_fiber`](thm.html#ModularCurve.SSHeckeV2.ord_heckeMultiplier_eq_and_width_eq_and_mem_ssPlaces_of_mem_fiber) and [`ModularCurve.SSHeckeV2.trace_heckeBetaC_mul_pow_mem_riemannRochSpace_weightDivisor`](thm.html#ModularCurve.SSHeckeV2.trace_heckeBetaC_mul_pow_mem_riemannRochSpace_weightDivisor).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ordDifferential_D_jGeomGen_eq_of_not_dvd_of_cast_natAbs_ne_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_CanonicalDivisor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open ModularCurve

theorem ModularCurve.ordDifferential_D_jGeomGen_eq_of_not_dvd_of_cast_natAbs_ne_zero
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    [∀ w : AlgebraicCurve.Place K ↥(modularFunctionFieldC K N), w.DCoordGenerates]
    [Nontrivial (Ω[↥(modularFunctionFieldC K N)⁄K])]
    (w : AlgebraicCurve.Place K ↥(modularFunctionFieldC K N)) :
    (IsAffineGeomPlace K N w →
      w.ordDifferential (KaehlerDifferential.D K ↥(modularFunctionFieldC K N) (jGeomGen K N))
        = (placeRamificationJ N w : ℤ) - 1) ∧
    (w.ord (jGeomGen K N) < 0 → (((w.ord (jGeomGen K N)).natAbs : ℕ) : K) ≠ 0 →
      w.ordDifferential (KaehlerDifferential.D K ↥(modularFunctionFieldC K N) (jGeomGen K N))
        = w.ord (jGeomGen K N) - 1) := by sorry
