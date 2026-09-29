-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mapDomain_sp_eq_ord_residue_alpha_full
-- name    : ModularCurve.JHPlaceSpecialization.ProlongationDatum.mapDomain_sp_eq_ord_residue_alpha_full
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/93509948-c097-5c5e-b28a-61f53d7e1194
-- title:
--   Specialization carries div(v) to div of its R₁-residue
-- statement:
--   Fix natural numbers $p$, $M$ with $p$ prime, $M\neq 0$, a subgroup $H\le(\mathbb Z/M)^\times$, and divisibility hypotheses $p\mid M$, $p^2\nmid M$, together with the assumption that every unit of $\mathbb Z/M$ reducing to $1$ in $(\mathbb Z/(M/p))^\times$ lies in $H$ (so $H$ is the full preimage of its image), and $M/p\neq 0$. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a non-unit of $A$, whose residue field $\kappa$ is algebraically closed of characteristic $p$. Let $F_M=\,$`xHFunctionFieldBar M H` and $F_{M/p}=\,$`xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)` be the Laurent-series base changes to $\overline{\mathbb Q}$ of the function fields at levels $(M,H)$ and $(M/p,\,$image of $H)$, let $\theta$ be a $\overline{\mathbb Q}$-algebra automorphism of $F_M$, and let $\alpha\colon F_{M/p}\to F_M$ be a $\overline{\mathbb Q}$-algebra map which leaves underlying $q$-expansions unchanged. Let `Psp` be a place specialization datum for $(p,M,H,A)$, with place map $\mathrm{sp}$ from places of $F_{M/p}$ over $\overline{\mathbb Q}$ to places of $\bar F=\,$`JHNeronObjectAtP.Fbar p M H hpM κ` over $\kappa$, and let `Rpd` be a prolongation datum for `Psp` and $\theta$, with regular prolongations $R_1,R_2$ of $A$ to $F_M$ with residue field $\bar F$. Then for every $v\in F_{M/p}$ such that $\alpha v$ lies in the valuation ring $R_1.\mathrm{integers}$ and $g:=R_1.\mathrm{residue}(\alpha v)\neq 0$, and every finitely supported divisor $D$ on the places of $F_{M/p}$ satisfying $D(w)=\mathrm{ord}_w(v)$ for all $w$, the pushforward of $D$ along $\mathrm{sp}$ satisfies $(\mathrm{sp}_*D)(v')=\mathrm{ord}_{v'}(g)$ for every place $v'$ of $\bar F$ over $\kappa$.
--
--   This is Deuring-style reduction of divisors in the form used here: the specialization map on places pushes the divisor of a level-$(M/p)$ function whose image in $F_M$ is a unit for the prolongation $R_1$ onto the divisor of its residue. It is invoked in the construction of the de Rham/differential model at $p$, in [`ModularCurve.XHDRModelAtP.exists_mapDomain_sp_eq_ord_and_ord_frob_eq_add_of_norm_of_prolongationDatum`](thm.html#ModularCurve.XHDRModelAtP.exists_mapDomain_sp_eq_ord_and_ord_frob_eq_add_of_norm_of_prolongationDatum).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mapDomain_sp_eq_ord_residue_alpha_full.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

theorem ModularCurve.JHPlaceSpecialization.ProlongationDatum.mapDomain_sp_eq_ord_residue_alpha_full
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ) :
    ∀ (v : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (h : α v ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨α v, h⟩ ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), (∀ w, D w = w.ord v) →
        ∀ v' : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
          Finsupp.mapDomain Psp.sp D v' = v'.ord (Rpd.R₁.residue ⟨α v, h⟩) := by sorry
