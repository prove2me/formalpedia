-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_isGoodDiv_reduce_notMem_isPrincipal_sub_of_smul_eq
-- name    : ModularCurve.JHPlaceSpecialization.exists_isGoodDiv_reduce_notMem_isPrincipal_sub_of_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/dd2220bc-a732-5a2c-90c9-853a59b88249
-- title:
--   Good effective divisors avoiding a finite set of fibre places
-- statement:
--   Fix a prime $p$ and $M \ne 0$ with $p \mid M$ but $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that reduces to $1$ in $(\mathbb{Z}/(M/p))^\times$, with $M/p \ne 0$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, whose residue field $\kappa$ is algebraically closed of characteristic $p$. Let $F_M = \overline{\mathbb{Q}}\cdot F(\Gamma_H(M))$ and $F_{M/p}$ the corresponding field for $M/p$ and the image subgroup `infSubgroup p M H hpM`, and let $\bar F$ be the $\kappa$-rational $q$-expansion field of level `JHNeronObjectAtP.ΓN p M H hpM`. Given: an automorphism $\theta$ of $F_M$ over $\overline{\mathbb{Q}}$; integral $\overline{\mathbb{Q}}$-algebra maps $\alpha, \beta : F_{M/p} \to F_M$, with $\alpha$ the identity on underlying Laurent series; a unit $pb$ of $\mathbb{Z}/(M/p)$ whose value is $p$; a self-map $\delta$ of the places of $\bar F$ given by the semilinear action of the diamond automorphism `diamondActionModL` at the $\Gamma_0(M/p)$-lift of $pb$; a finite set $SS$ whose members are exactly the pairs $(\varphi v, v)$ with $v$ supersingular, $\varphi$ the mod-$p$ Frobenius place map; a specialization datum `Psp` of type `JHPlaceSpecialization p M H hpM A`; the type dichotomy for $(\alpha,\beta,\delta)$, asserting for every place $W$ of $F_M$ that either $\mathrm{red}_1 W = \varphi(\mathrm{red}_2 W)$ or $\delta(\varphi(\mathrm{red}_1 W)) = \mathrm{red}_2 W$; and finiteness of the locus $\{v : \varphi(\delta(\varphi v)) = v\}$. Then for every finite set $T$ of places of $\bar F$ there are divisors $E_0, C_0$ on $F_M$ with $E_0 \ge 0$ of positive degree, every place in the support of $E_0$ strict of the first or second type, both readings $\mathrm{red}_1 V, \mathrm{red}_2 V$ outside $T$ for $V$ in that support, $C_0 \ge 0$ of positive degree and fixed by the arithmetic Galois action of every element of the inertia subgroup of $A$ over $\mathbb{Q}$, and $E_0 - C_0$ principal.
--
--   This is the moving lemma of the level-lowering argument at a prime $p$ exactly dividing the level on the curve $X_H(M)$: it produces effective divisors of positive degree whose points are all strict for the two reduction maps, avoid any prescribed finite set of places in the fibre at $p$, and are principally equivalent to an inertia-invariant effective divisor. It feeds the construction of classes in $\mathrm{Pic}^0$ used by [`ModularCurve.XHDRModelAtP.exists_pic0Mk_eq_forall_isStrict_or_reduceFst_mem_of_prolongationDatum_offDiag_of_wgen`](thm.html#ModularCurve.XHDRModelAtP.exists_pic0Mk_eq_forall_isStrict_or_reduceFst_mem_of_prolongationDatum_offDiag_of_wgen).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_exists_isGoodDiv_reduce_notMem_isPrincipal_sub_of_smul_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

theorem ModularCurve.JHPlaceSpecialization.exists_isGoodDiv_reduce_notMem_isPrincipal_sub_of_smul_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)
    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p)
    (Psp : JHPlaceSpecialization p M H hpM A)
    (hTD : Psp.TypeDichotomy α β hα hβ δ)
    (hFix : {v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) | JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v}.Finite)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ))) :
    ∀ T : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))),
      ∃ E₀ C₀ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        (∀ V, 0 ≤ E₀ V) ∧ Psp.IsGoodDiv α β hα hβ δ E₀ ∧
          (∀ V ∈ E₀.support, Psp.reduceFst α hα V ∉ T ∧ Psp.reduceSnd β hβ δ V ∉ T) ∧
            0 < Divisor.degree E₀ ∧ (∀ V, 0 ≤ C₀ V) ∧
              (∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • C₀ = C₀) ∧
                0 < Divisor.degree C₀ ∧ Divisor.IsPrincipal (E₀ - C₀) := by sorry
