-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_regularityLaw_of_orderLawFixed_of_typeDichotomy_of_prolongationDatum
-- name    : ModularCurve.XHDRModelAtP.regularityLaw_of_orderLawFixed_of_typeDichotomy_of_prolongationDatum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/ebb37450-47e7-5f79-95ad-109e60897e66
-- title:
--   Regularity law from order law and type dichotomy
-- statement:
--   Fix a prime $p$ and $M$ with $p \mid M$ but $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that maps to $1$ under reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$, and $j$ lying in the level-one $q$-expansion function field over $\mathbb{Q}$; let $\mathfrak{X}$ be a datum `XHDRModelAtP` for $X_H(M)$ at $p$. Further data: a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ a non-unit, whose residue field $\kappa$ is algebraically closed of characteristic $p$; a ring map $\rho : R_p \to A$ compatible with $R_p \to \overline{\mathbb{Q}}$; a unit $pb$ of $\mathbb{Z}/(M/p)$ reducing to $p$; the self-map $\delta$ of places of $\bar F =$ `Fbar` given by the semilinear action of the diamond automorphism attached to a $\Gamma_0(M/p)$-lift of $pb$; a finset $SS$ whose members are exactly the pairs $(\mathrm{Frob}\,w, w)$ with $w$ supersingular; an $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of $F_M =$ `xHFunctionFieldBar M H` realising, on places, the effect of the involution $\mathfrak{X}.w$ on $\overline{\mathbb{Q}}$-points of $\mathfrak{X}.\mathrm{Meta}$; an integral degeneracy map $\alpha : F_{M/p} \to F_M$ with $\theta \circ \alpha$ integral, acting as the identity on $q$-expansions; a specialization kit `Psp` and a prolongation datum `Rpd` $=(R_1,R_2)$ for $\theta$; the hypothesis `hcomp` identifying the place of a closed point of the fibre model lying over the reduction of a point $y$ with $\mathrm{red}_1 = \mathrm{sp}(\cdot \restriction \alpha)$ for $i=0$ and with $\mathrm{red}_2 = \delta(\mathrm{sp}(\cdot \restriction \theta\alpha))$ for $i=1$; an element $x \in F_M$ with $q$-expansion $j$; the order law `OrderLawFixed` and the type dichotomy (for every place $W$ of $F_M$, either $\mathrm{red}_1 W = \mathrm{Frob}(\mathrm{red}_2 W)$ or $\delta(\mathrm{Frob}(\mathrm{red}_1 W)) = \mathrm{red}_2 W$); and stability of affineness under $v \mapsto \delta(\mathrm{Frob}\,v)$. The conclusion is `RegularityLaw`: first, for every $f \in F_M$ lying in both $R_1$ and $R_2$ and every place $v$ of $\bar F$ satisfying the predicate `Fixed` for $\delta$ and affine (some $y \in \bar F$ with $q$-expansion $j$ has a $v$-value), if $\mathrm{ord}_V f \ge 0$ for all places $V$ of $F_M$ with $\mathrm{red}_1 V = v$, then $\mathrm{ord}_v$ of the $R_1$-residue of $f$ is $\ge 0$ whenever that residue is non-zero, and $\mathrm{ord}_{\delta(\mathrm{Frob}\,v)}$ of the $R_2$-residue of $f$ is $\ge 0$ whenever that residue is non-zero; second, for such $f$ and every pair $s \in SS$, if $\mathrm{ord}_V f \ge 0$ for all $V$ with $\mathrm{red}_1 V = s_1$, then there is $c \in \kappa$ which is simultaneously the value of the $R_1$-residue of $f$ at $s_1$ and of the $R_2$-residue of $f$ at $s_2$.
--
--   This is the regularity law of the place-specialization kit for $X_H(M)$ at a prime exactly dividing the level: integrality of a function on both branches of the reduced curve propagates to non-negativity of orders at fixed affine places, and at a supersingular node pair the two branch residues take a common value. It feeds the construction of the specialization kit together with its prolongation datum, glued specialization and component-group data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_regularityLaw_of_orderLawFixed_of_typeDichotomy_of_prolongationDatum.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.regularityLaw_of_orderLawFixed_of_typeDichotomy_of_prolongationDatum
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hcomp : ∀ (i : Fin 2)
      (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
      (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
      (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
      (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
        if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
        else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y))

    (x : ↥(xHFunctionFieldBar M H)) (hx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))

    (hO : Rpd.OrderLawFixed α (θ.toAlgHom.comp α) hα hβ δ)
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ)
    (haff : ∀ v, JHPlaceSpecialization.IsAffinePlace p M H hpM A v →
      JHPlaceSpecialization.IsAffinePlace p M H hpM A (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p v))) :
    Rpd.RegularityLaw α (θ.toAlgHom.comp α) hα hβ δ SS := by sorry
