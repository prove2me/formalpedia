-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_jHPlaceSpecialization_prolongationDatum_gluedSpecialization_componentGroup_offDiag_of_wgen
-- name    : ModularCurve.XHDRModelAtP.exists_jHPlaceSpecialization_prolongationDatum_gluedSpecialization_componentGroup_offDiag_of_wgen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/77b8b1ee-411c-5a63-852b-29c8adf99e5b
-- title:
--   Place-specialization kit for X_H(M) at p ∥ M
-- statement:
--   Fix a prime $p$ and a nonzero level $M$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing the kernel of reduction to $(\mathbb{Z}/(M/p))^\times$, with $M/p$ nonzero, and assume $j$ lies in the $q$-expansion function field at full level, so that the two-chart integral models are available; let $\mathfrak{X}$ be an integral model datum `XHDRModelAtP` for $X_H(M)$ over $R p$, carrying in particular a curve model `Meta` of $\overline{\mathbb{Q}}\cdot F(\Gamma_H(M))$ identified with the geometric generic fibre and the involution `w`. The further data are: a $\overline{\mathbb{Q}}$-algebra automorphism $\theta_0$ of $\overline{\mathbb{Q}}\cdot F(\Gamma_H(M))$ which, on Laurent series, sends any element agreeing with a level-$(M/p)$ function $u(q)$ to $u(q^p)$, and which transports $\overline{\mathbb{Q}}$-points along `w` in the sense that $y' \circ \mathfrak{X}.\mathrm{eeta} \circ \mathrm{pullback.fst} \circ w = y \circ \mathfrak{X}.\mathrm{eeta} \circ \mathrm{pullback.fst}$ forces the associated places to satisfy $\mathrm{pointEquivPlace}\,y' = \theta_0 \cdot \mathrm{pointEquivPlace}\,y$; a valuation subring $A \subseteq \overline{\mathbb{Q}}$ in which $p$ is a nonunit, with algebraically closed residue field $\kappa$ of characteristic $p$, and a ring map $\rho : R p \to A$ compatible with the structure map to $\overline{\mathbb{Q}}$; a unit $pb$ of $\mathbb{Z}/(M/p)$ represented by $p$, and the self-map $\delta$ of the places of $\bar{F} = \kappa\cdot F(\Gamma_N)$ given by the diamond automorphism `diamondActionModL` at a $\Gamma_0$-lift of $pb$; and a finset $SS$ whose members are exactly the supersingular node pairs $(\mathrm{Frob}\,v, v)$. The conclusion asserts the existence of an integral $\overline{\mathbb{Q}}$-algebra map $\alpha$ from the level-$(M/p)$ function field into the level-$M$ one, with $\beta = \theta_0 \circ \alpha$ also integral, a place specialization $Psp$ of type `JHPlaceSpecialization` at $A$, a prolongation datum $Rpd$ over $Psp$ and $\theta_0$ (two regular prolongations, the first computing residues by coefficientwise reduction of Laurent series, the second obtained from the first through $\theta_0$), an additive map $spJ$ from the inertia invariants of $J_H(M)$ (classes fixed by the inertia subgroup of $A$ over $\mathbb{Q}$) to the glued Picard group $\mathrm{GluedPic}^0(\kappa, \bar F, SS)$, widths $e : SS \to \mathbb{N}$ and an additive map `comp` to the component group $\mathrm{Dual}_{\mathbb{Z}}(\text{character lattice})/\mathrm{range}(\mathrm{gramMap}\,e)$, such that: the $w$-transport property of $\theta_0$ holds and $\theta_0$ commutes with the arithmetic Galois action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$; $\alpha u$ has the Laurent series of $u$ and $\beta u$ the series $u(q^p)$; the predicates `TypeDichotomy`, `IsModel`, `OrderLawFixed`, `RegularityLaw` and `NodeValueLaw` for $(\alpha,\beta,\delta,SS)$ hold, and $spJ$ is a glued specialization; every $e s$ is positive, `comp` is surjective, and $\mathrm{comp}\,x = 0$ exactly for the good classes $x$; finally, for each $i \in \{0,1\}$, each $\overline{\mathbb{Q}}$-point $y$ of `Meta`, each $A$-section $u$ of the model compatible with $y$ through `barPt`, each $\kappa$-section $u\kappa$ of the fibre reducing $u$, and each closed point $P_0$ of the fibre curve model $\mathfrak{X}.\mathrm{Mfib}$ lying over the closed point of $u\kappa$ along the $i$-th component map, the place of $P_0$ equals $\mathrm{reduceFst}\,\alpha$ of the place of $y$ when $i = 0$ and $\mathrm{reduceSnd}\,\beta\,\delta$ of it otherwise, while conversely the other of these two reductions of the place of $y$ is obtained from the place of $P_0$ by the mod-$p$ Frobenius on places, composed with $\delta$ in the case $i = 0$.
--
--   This packages the specialization theory of the Deligne–Rapoport model of $X_H(M)$ at a prime $p$ exactly dividing $M$: the reduction of places of the function field to the two components of the special fibre, their gluing along the supersingular points, and the resulting surjection from the inertia-invariant part of $J_H(M)$ onto a component group whose kernel consists of the good classes. It is used to bound the order of the inertia-invariant torsion of $J_H(M)$ and to characterise the points reducing into the finite part, the inputs to the Ribet-style level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_jHPlaceSpecialization_prolongationDatum_gluedSpecialization_componentGroup_offDiag_of_wgen.lean

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

theorem ModularCurve.XHDRModelAtP.exists_jHPlaceSpecialization_prolongationDatum_gluedSpecialization_componentGroup_offDiag_of_wgen
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (θ₀ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθ₀ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ₀ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hwgen₀ : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ₀ • 𝔛.Meta.pointEquivPlace y)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p) :
    ∃ (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
      (hα : α.IsIntegral)
      (hβ : (θ₀.toAlgHom.comp α).IsIntegral)
      (Psp : JHPlaceSpecialization p M H hpM A)
      (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ₀)
      (spJ : ↥(JHPlaceSpecialization.inertiaInvariants M H A) →+
        GluedPic0 (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) SS)
      (e : ↥SS → ℕ)
      (comp : ↥(JHPlaceSpecialization.inertiaInvariants M H A) →+ componentGroup e),

      (∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ₀ • 𝔛.Meta.pointEquivPlace y) ∧

      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
          θ₀ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) =
            arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ₀ f) ∧

      (∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ))) ∧

      (∀ u, (((θ₀.toAlgHom.comp α) u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ))) ∧

      Psp.TypeDichotomy α (θ₀.toAlgHom.comp α) hα hβ δ ∧
      Rpd.IsModel α (θ₀.toAlgHom.comp α) hα hβ δ ∧
      Rpd.OrderLawFixed α (θ₀.toAlgHom.comp α) hα hβ δ ∧
      Rpd.RegularityLaw α (θ₀.toAlgHom.comp α) hα hβ δ SS ∧
      Rpd.NodeValueLaw α (θ₀.toAlgHom.comp α) hα hβ δ SS ∧
      Psp.IsGluedSpecialization α (θ₀.toAlgHom.comp α) hα hβ δ SS spJ ∧

      (∀ s, 0 < e s) ∧ Function.Surjective comp ∧
      (∀ x : ↥(JHPlaceSpecialization.inertiaInvariants M H A),
        comp x = 0 ↔ Psp.IsGoodClass α (θ₀.toAlgHom.comp α) hα hβ δ SS (x : JH M H)) ∧

      (∀ (i : Fin 2)
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
          else Psp.reduceSnd (θ₀.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y)) ∧

      (∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        if i = 0 then
          Psp.reduceSnd (θ₀.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y) =
            δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))
        else
          Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y) =
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0)) := by sorry
