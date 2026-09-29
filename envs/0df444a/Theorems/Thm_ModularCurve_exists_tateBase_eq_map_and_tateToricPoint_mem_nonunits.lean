-- Prove2me | Theorems.Thm_ModularCurve_exists_tateBase_eq_map_and_tateToricPoint_mem_nonunits
-- name    : ModularCurve.exists_tateBase_eq_map_and_tateToricPoint_mem_nonunits
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/538b8ec3-8831-5a4d-93db-8ad1bd361e10
-- title:
--   Tate curve over the Gauss ring: smooth model and toric point
-- statement:
--   Let $L$ be a field, $A_0 \subseteq L$ a valuation subring, $L_2$ a subfield of the Laurent series field $L(\!(q)\!)$ and $W_2$ a valuation subring of $L_2$, subject to three membership presentations: $f \in L_2$ exactly when $f\,y = x$ in $L(\!(q)\!)$ for some power series $x,y$ over $A_0$ with $y \neq 0$ (coefficients pushed into $L$ and read as Laurent series); $f \in W_2$ exactly when such a relation holds with the reduction of $y$ modulo the maximal ideal of $A_0$ non-zero; and $f$ lies in the set of non-units of $W_2$ exactly when such a relation holds with the reduction of $y$ non-zero and that of $x$ zero. Let $p$ be a non-zero natural number and $c \in A_0^{\times}$ with $1 - c$ in the maximal ideal of $A_0$ and with image $c \neq 1$ in $L$. The conclusion has two parts. First, there is a Weierstrass curve $T$ over $W_2$ whose base change along $W_2 \subseteq L_2 \subseteq L(\!(q)\!)$ is [`ModularCurve.tateBase L p`](def/ModularCurve_TateSlots.html#L46), the Tate Weierstrass curve with integral power series coefficients transported to $L(\!(q)\!)$ and then subjected to the substitution multiplying $q$-exponents by $p$, and such that the reduction of $T$ modulo the maximal ideal of $W_2$ has non-zero discriminant $\Delta$. Secondly, there are $x_t, y_t \in L_2$ whose images in $L(\!(q)\!)$ are the first and second components of [`ModularCurve.tateToricPoint L p c`](def/ModularCurve_KatzLevelPCusps.html#L20), the explicit pair of power series with constant terms $c\,(1-c)^{-2}$ and $c^{2}(1-c)^{-3}$ and with $m$-th coefficients ($m \geq 1$) $\sum_{d \mid m,\ p \mid d} (m/d)\bigl(c^{m/d} + c^{-m/d}\bigr) - 2\,[p \mid m]\sum_{e \mid m/p} e$ and $\sum_{d \mid m,\ p \mid d}\bigl(\binom{m/d}{2}c^{m/d} - \binom{m/d+1}{2}c^{-m/d}\bigr) + [p \mid m]\sum_{e \mid m/p} e$, and these satisfy $y_t \neq 0$ with both $x_t/y_t$ and $y_t^{-1}$ non-units of $W_2$, i.e. in its maximal ideal.
--
--   This is the statement that the Tate curve with parameter $q^p$ descends to a Weierstrass model over the Gauss valuation ring of $L(\!(q)\!)$ with smooth (non-degenerate) reduction, and that the toric point with coordinate $u = c$, for $c$ a unit congruent to $1$ but distinct from $1$, reduces to the origin, its origin-chart parameters $x_t/y_t$ and $1/y_t$ lying in the Gauss maximal ideal. It feeds the construction of origin charts at the cusps for full level structures, in the form used for the Tate point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_tateBase_eq_map_and_tateToricPoint_mem_nonunits.lean

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.exists_tateBase_eq_map_and_tateToricPoint_mem_nonunits
    (L : Type) [Field L] (A₀ : ValuationSubring L)
    (L₂ : Subfield (LaurentSeries L)) (W₂ : ValuationSubring ↥L₂)
    (hL₂ : ∀ f : LaurentSeries L, f ∈ L₂ ↔ ∃ x y : PowerSeries ↥A₀, y ≠ 0 ∧
      f * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap ↥A₀ L)) = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap ↥A₀ L)))
    (hW₂ : ∀ f : ↥L₂, f ∈ W₂ ↔ ∃ x y : PowerSeries ↥A₀, y.map (IsLocalRing.residue ↥A₀) ≠ 0 ∧
      ((f : ↥L₂) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap ↥A₀ L)) =
        HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap ↥A₀ L)))
    (hW₂' : ∀ f : ↥L₂, f ∈ W₂.nonunits ↔ ∃ x y : PowerSeries ↥A₀, y.map (IsLocalRing.residue ↥A₀) ≠ 0 ∧
      x.map (IsLocalRing.residue ↥A₀) = 0 ∧
      ((f : ↥L₂) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap ↥A₀ L)) =
        HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap ↥A₀ L)))
    (p : ℕ) [NeZero p] (c : (↥A₀)ˣ) (hc : 1 - (c : ↥A₀) ∈ IsLocalRing.maximalIdeal ↥A₀) (hc1 : ((c : ↥A₀) : L) ≠ 1) :

    (∃ T : WeierstrassCurve ↥W₂,
      (T.map W₂.subtype).map L₂.subtype = ModularCurve.tateBase L p ∧
      (T.map (IsLocalRing.residue ↥W₂)).Δ ≠ 0) ∧

    (∃ xt yt : ↥L₂,
      ((xt : ↥L₂) : LaurentSeries L) = (ModularCurve.tateToricPoint L p (Units.map (A₀.subtype : ↥A₀ →* L) c)).1 ∧
      ((yt : ↥L₂) : LaurentSeries L) = (ModularCurve.tateToricPoint L p (Units.map (A₀.subtype : ↥A₀ →* L) c)).2 ∧
      yt ≠ 0 ∧ xt / yt ∈ W₂.nonunits ∧ yt⁻¹ ∈ W₂.nonunits) := by sorry
