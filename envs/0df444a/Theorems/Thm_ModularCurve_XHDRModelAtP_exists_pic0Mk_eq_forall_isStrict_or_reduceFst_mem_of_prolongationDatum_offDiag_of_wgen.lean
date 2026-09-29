-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_pic0Mk_eq_forall_isStrict_or_reduceFst_mem_of_prolongationDatum_offDiag_of_wgen
-- name    : ModularCurve.XHDRModelAtP.exists_pic0Mk_eq_forall_isStrict_or_reduceFst_mem_of_prolongationDatum_offDiag_of_wgen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/88161b2d-1fb5-5aed-bbd1-a250035aef09
-- title:
--   Moving a class of J_H(M) off δ-fixed places
-- statement:
--   Fix a prime $p$ and $M$ with $p \mid M$ but $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that reduces to $1$ in $(\mathbb{Z}/(M/p))^\times$, and the hypothesis `hj` that $j$, as a $q$-series, lies in the level-$1$ $q$-expansion function field; let $\mathfrak{X}$ be a datum `XHDRModelAtP p M H hpM hj`, which packages an integral model of $X_H(M)$ over $R p$ (proper, flat, normal, with smooth model at level $\Gamma_N$) together with a curve model `Meta` over $\overline{\mathbb{Q}}$ with function field $FM =$ `xHFunctionFieldBar M H` and a comparison isomorphism `eeta`. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit, with algebraically closed residue field $\kappa$ of characteristic $p$, and $\rho : R p \to A$ lifting the structure map to $\overline{\mathbb{Q}}$. Let $pb$ be a unit of $\mathbb{Z}/(M/p)$ represented by $p$, and $\delta$ the action on places of $Fb =$ `JHNeronObjectAtP.Fbar p M H hpM κ` of the diamond automorphism attached to $pb$ at level $M/p$ with group `infSubgroup p M H hpM`; let $SS$ be a finite set whose members are exactly the pairs $(w',w)$ with $w$ supersingular and $w'$ the mod-$p$ Frobenius place of $w$. Let $\theta$ be a $\overline{\mathbb{Q}}$-algebra automorphism of $FM$, $\alpha : FMp \to FM$ an integral $\overline{\mathbb{Q}}$-algebra map from the function field at level $M/p$ with $\theta \circ \alpha$ integral, $Psp$ a place-specialisation datum (a map $sp$ on places and a compatible map on degree-zero divisor classes satisfying the divisor, surjectivity, inertia and Frobenius laws), and $Rpd$ a prolongation datum for $Psp$ and $\theta$ (two regular prolongations $R_1, R_2$ of $A$ to $FM$ with residues in $Fb$, related by $\theta$). Assume: `hwgen`, that two $\overline{\mathbb{Q}}$-points of `Meta.C` related by $\mathfrak{X}.w$ have places related by $\theta$; `hα_coe`, that $\alpha$ preserves $q$-expansions, and `hβ_coe`, that $\theta \circ \alpha$ replaces $q$ by $q^p$; `hTD`, that every place $W$ of $FM$ satisfies $\mathrm{red}_1(W) = \mathrm{Frob}(\mathrm{red}_2(W))$ or $\delta(\mathrm{Frob}(\mathrm{red}_1(W))) = \mathrm{red}_2(W)$, where $\mathrm{red}_1(W) = sp(W|_\alpha)$ and $\mathrm{red}_2(W) = \delta(sp(W|_{\theta \circ \alpha}))$; `hmodel`, the two divisor laws and the two cusp laws; `hcompat` and `hcompat'`, which identify, for each index $i \in \{0,1\}$ and each closed point of the fibre curve model lying under a $\kappa$-point coming from an $A$-section through a given $\overline{\mathbb{Q}}$-point $y$, the place of that point with $\mathrm{red}_1$ or $\mathrm{red}_2$ of the place of $y$ (and the complementary identity with a Frobenius place inserted); `hO`, the order law at $\delta$-fixed affine places; `hRL` and `hNV`, the regularity and node-value laws at $SS$; and `hθgal`, that $\theta$ commutes with the arithmetic Galois action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on $FM$. Then for every class $x$ in $J_H(M) = \mathrm{Pic}^0_{\overline{\mathbb{Q}}}(FM)$ there is a degree-zero divisor $E$ with $[E] = x$ such that each place $V$ in the support of $E$ either satisfies $\delta(\mathrm{Frob}(\mathrm{red}_1(V))) = \mathrm{red}_2(V)$ with $\mathrm{red}_1(V)$ not `Fixed` for $\delta$, or satisfies $\mathrm{red}_1(V) = \mathrm{Frob}(\mathrm{red}_2(V))$ with $\mathrm{red}_2(V)$ not `Fixed`, or has $\mathrm{red}_1(V) = s_1$ for some $s \in SS$.
--
--   This is the moving lemma for the Jacobian of $X_H(M)$ at a prime exactly dividing the level: every divisor class is represented by a divisor whose places reduce either to non-fixed points of one of the two components of the special fibre, in the strict sense recorded by `IsStrictFst` and `IsStrictSnd`, or into the tubes over the supersingular crossings indexed by $SS$. It is used by [`ModularCurve.XHDRModelAtP.isGoodClass_of_forall_dvd_ord_residue_of_annulus_offDiag_of_wgen`](thm.html#ModularCurve.XHDRModelAtP.isGoodClass_of_forall_dvd_ord_residue_of_annulus_offDiag_of_wgen) as the first step in the analysis of the component group and the specialisation of divisor classes at $p \,\|\, M$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_pic0Mk_eq_forall_isStrict_or_reduceFst_mem_of_prolongationDatum_offDiag_of_wgen.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_pic0Mk_eq_forall_isStrict_or_reduceFst_mem_of_prolongationDatum_offDiag_of_wgen
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
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ) (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ)

    (hcompat : ∀ (i : Fin 2)
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
    (hcompat' : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        if i = 0 then
          Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y) =
            δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))
        else
          Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y) =
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))

    (hO : Rpd.OrderLawFixed α (θ.toAlgHom.comp α) hα hβ δ)
    (hRL : Rpd.RegularityLaw α (θ.toAlgHom.comp α) hα hβ δ SS) (hNV : Rpd.NodeValueLaw α (θ.toAlgHom.comp α) hα hβ δ SS)

    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) =
        arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)

    (hβ_coe : ∀ u, (((θ.toAlgHom.comp α) u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (x : JH M H) :
    ∃ E : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))),
      Pic0.mk E = x ∧
      ∀ V ∈ (E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support,
        Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V ∨
          ∃ s ∈ SS, Psp.reduceFst α hα V = s.1 := by sorry
