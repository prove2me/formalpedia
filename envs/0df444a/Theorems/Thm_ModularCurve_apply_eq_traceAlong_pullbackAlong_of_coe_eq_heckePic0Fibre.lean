-- Prove2me | Theorems.Thm_ModularCurve_apply_eq_traceAlong_pullbackAlong_of_coe_eq_heckePic0Fibre
-- name    : ModularCurve.apply_eq_traceAlong_pullbackAlong_of_coe_eq_heckePic0Fibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/e4afb1aa-250d-513d-a40a-f4177ae5f7d5
-- title:
--   Serre's δ intertwines ̄ T_q with tr_α∘β^*
-- statement:
--   Let $K$ be an algebraically closed field of characteristic a prime $p$, let $N\ge 1$ with $p\nmid N$, and let $q$ be a prime with $q\ne p$. Write $F=\mathtt{modularFunctionFieldC}\ K\ N$, the intermediate field of $K((t))$ generated over $K$ by $\mathtt{jqModC}\ K$ and $\mathtt{jqNModC}\ K\ N$, and let $\mathrm{Pic}^0(K,F)$ be the group of divisors of degree zero (finitely supported $\mathbb Z$-valued functions on the places of $F$ over $K$, a place being a non-trivial valuation subring of $F$ containing $K$ which is a principal ideal ring) modulo principal divisors. Let $\delta$ be an additive map from the $p$-torsion subgroup of $\mathrm{Pic}^0(K,F)$ to $\Omega_{F/K}$ satisfying Serre's recipe: whenever a degree-zero divisor $E$ represents the class of a $p$-torsion element $y$ and $g\in F^\times$ satisfies $p\,E(v)=\operatorname{ord}_v g$ at every place $v$, then $\delta y=g^{-1}\,dg$. Let $x,y$ be $p$-torsion classes with $y=\mathtt{heckePic0Fibre}\ K\ N\ q$ applied to $x$, i.e. $y$ is the image of $x$ under the endomorphism of $\mathrm{Pic}^0(K,F)$ descended from the divisor correspondence attached to the two degeneracy embeddings of $F$ into $\mathtt{charLDegeneracyRoof}\ K\ N\ q$ (the inclusion $\alpha=\mathtt{heckeAlphaC}$ and the map $\beta=\mathtt{heckeBetaC}$ induced on $q$-expansions by $\mathtt{qExpand}\ K\ q$). Then $\delta y=\operatorname{tr}_\alpha(\beta^*(\delta x))$, where $\beta^*$ is the map on Kähler differentials induced by $\beta$ and $\operatorname{tr}_\alpha$ is the trace map along $\alpha$ (given by the field trace through the formally étale base-change identification of differentials when $\alpha$ is separable, and zero otherwise).
--
--   This is the compatibility of Serre's logarithmic-derivative map $\delta$ on the $p$-torsion of $\mathrm{Pic}^0$ in characteristic $p$ with the Hecke correspondence $\bar T_q$ at a prime $q\ne p$, for the modular function field of level $N$ realised inside Laurent series. It is the form in which the Hecke action is transported to differentials, and is used in [`ModularCurve.pullbackAlong_apply_mem_mTorsionDiffOf_of_mem_heckeTorsion_jZero_of_coe_eq_reductionModL`](thm.html#ModularCurve.pullbackAlong_apply_mem_mTorsionDiffOf_of_mem_heckeTorsion_jZero_of_coe_eq_reductionModL).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_apply_eq_traceAlong_pullbackAlong_of_coe_eq_heckePic0Fibre.lean

import Mathlib
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open ModularCurve AlgebraicCurve

theorem ModularCurve.apply_eq_traceAlong_pullbackAlong_of_coe_eq_heckePic0Fibre
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (q : ℕ) [NeZero q] [Fact q.Prime] (hqp : q ≠ p)
    (δ : Pic0.torsion K (modularFunctionFieldC K N) p →+ Ω[↥(modularFunctionFieldC K N)⁄K])
    (hδ : ∀ (y : Pic0.torsion K (modularFunctionFieldC K N) p)
        (E : Divisor.degZero (K := K) (F := modularFunctionFieldC K N)) (g : modularFunctionFieldC K N),
        Pic0.mk E = (y : Pic0 K (modularFunctionFieldC K N)) → g ≠ 0 →
        (∀ v : Place K (modularFunctionFieldC K N),
          (p : ℤ) * (E : Divisor K (modularFunctionFieldC K N)) v = v.ord g) →
        δ y = g⁻¹ • KaehlerDifferential.D K (modularFunctionFieldC K N) g)
    (x y : Pic0.torsion K (modularFunctionFieldC K N) p)
    (hy : (y : Pic0 K (modularFunctionFieldC K N)) =
      heckePic0Fibre K N q (x : Pic0 K (modularFunctionFieldC K N))) :
    δ y = Differential.traceAlong (heckeAlphaC K N q)
      (Differential.pullbackAlong (heckeBetaC K N q) (δ x)) := by sorry
