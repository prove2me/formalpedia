-- Prove2me | Theorems.Thm_ModularCurve_exists_coe_eq_thetaL_jqModC_zpow_and_stackOrd_eq
-- name    : ModularCurve.exists_coe_eq_thetaL_jqModC_zpow_and_stackOrd_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/2b5d3394-6205-5fab-89cc-2142c3f741a7
-- title:
--   Hasse invariant as (thetajmath̄)^{-(p-1)/2} on level N
-- statement:
--   Let $p\ge 5$ be a prime, let $N\ge 1$ be an integer with $p\nmid N$, and let $K$ be an algebraically closed field of characteristic $p$. Write $F_N=K(\bar\jmath,\bar\jmath_N)\subseteq K((q))$ for `modularFunctionFieldC K N`, the subfield of the Laurent series field generated over $K$ by $\bar\jmath=$ `jqModC K` $=q^{-1}\cdot(\text{the integral } j\text{-numerator series})$ and by its $N$-fold $q$-substitution $\bar\jmath_N=$ `jqNModC K N`. The assertion is that there is an element $h\in F_N$ whose $q$-expansion equals $\theta(\bar\jmath)^{-(p-1)/2}$, where $\theta f=q\,df/dq$ and the exponent is the integer $-((p-1)/2)$ (integer division), such that two further properties hold. First, for every place $x$ of $F_N$ over $K$ (a proper valuation subring of $F_N$ containing $K$ whose ring is a principal ideal ring) at which both $\bar\jmath$ and $\bar\jmath_N$ are regular, one has $\mathrm{stackOrd}_N^{(p-1)/2}(h,x)=1$ if $x$ lies in `ssPlaces p N K`, i.e. $x$ has residue degree $1$, is affine in the above sense, and the value $\bar\jmath(x)\in K$ lies in `ssJSet p K`, and $\mathrm{stackOrd}_N^{(p-1)/2}(h,x)=0$ otherwise; here $\mathrm{stackOrd}_N^{m}(h,x)=\mathrm{placeWidth}_N(x)\cdot\mathrm{ord}_x(h)+m\,(\mathrm{jWidth}(\bar\jmath(x))-1)$, with $\mathrm{jWidth}(j)=3,2,1$ according as $j=0$, $j=1728$, or neither, and $\mathrm{placeWidth}_N(x)=\mathrm{jWidth}(\bar\jmath(x))/\mathrm{placeRamificationJ}\,N\,x$ (division in $\mathbb N$). Second, at every place $x$ with $\mathrm{ord}_x(\bar\jmath)<0$ one has $\mathrm{ord}_x(h)=\tfrac{p-1}{2}\cdot(-\mathrm{ord}_x(\bar\jmath))$.
--
--   This is the function-field incarnation of the Hasse invariant $A\equiv E_{p-1}\pmod p$ on the modular curve of level $N$ in characteristic $p$: written against $(d\bar\jmath)^{(p-1)/2}$ it has $q$-expansion $\theta(\bar\jmath)^{-(p-1)/2}$, simple zeros on the moduli stack exactly at the supersingular places (Igusa's theorem), no other affine zeros, and prescribed order at the cusps. It feeds the mod $p$ theory of modular forms used later, in particular the computations of orders and greatest common divisors attached to Eisenstein ratios and the characterisation of mod $p$ forms by their $q$-expansions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_coe_eq_thetaL_jqModC_zpow_and_stackOrd_eq.lean

import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_ModPFormFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_coe_eq_thetaL_jqModC_zpow_and_stackOrd_eq
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] :
    ∃ h : ↥(modularFunctionFieldC K N),
      (h : LaurentSeries K) = thetaL K (jqModC K) ^ (-(((p : ℤ) - 1) / 2)) ∧
      (∀ x : Place K (modularFunctionFieldC K N), IsAffineGeomPlace K N x →
          (x ∈ ssPlaces p N K → stackOrd N (((p : ℤ) - 1) / 2) h x = 1) ∧
          (x ∉ ssPlaces p N K → stackOrd N (((p : ℤ) - 1) / 2) h x = 0)) ∧
      (∀ x : Place K (modularFunctionFieldC K N), x.ord (jGeomGen K N) < 0 →
          x.ord h = (((p : ℤ) - 1) / 2) * (-(x.ord (jGeomGen K N)))) := by sorry
