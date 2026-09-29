-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_mem_range_stalk_read_of_mem_integers_of_forall_isStrictFst_mem
-- name    : ModularCurve.XHDRModelAtP.mem_range_stalk_read_of_mem_integers_of_forall_isStrictFst_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/4bf5eb1f-c5e7-5efe-a0f9-e10e5c84b4c5
-- title:
--   Hartogs criterion for germs at a smooth special-fibre point
-- statement:
--   Fix a prime $p$, a level $M$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that reduces to $1$ in $(\mathbb{Z}/(M/p))^\times$, and the hypothesis $hj$ that `jqModC ℚ` lies in the level-$\mathrm{SL}(2,\mathbb{Z})$ $q$-expansion function field over $\mathbb{Q}$; let $\mathfrak{X}$ be an `XHDRModelAtP p M H hpM hj` package, carrying in particular a curve model $\mathfrak{X}.\mathrm{Meta}$ of $\overline{\mathbb{Q}}\cdot F_H(M) =$ `xHFunctionFieldBar M H` together with an isomorphism `eeta` onto the base change of the integral model to $\overline{\mathbb{Q}}$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, residue field $\kappa$ algebraically closed of characteristic $p$, and $\rho : R_p \to A$ lifting the structure map to $\overline{\mathbb{Q}}$. Further data: a unit $pb$ of $\mathbb{Z}/(M/p)$ represented by $p$; the map $\delta$ on places of `Fbar` given by the diamond automorphism attached to $pb$ at level $M/p$ acting through `SemilinearAut.ofAlgAut`; a finset $SS$ whose members are exactly the supersingular node pairs `ssNodePairsQExp`; an $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of `xHFunctionFieldBar M H`; an integral $\overline{\mathbb{Q}}$-algebra map $\alpha$ from level $M/p$ to level $M$, with $\theta \circ \alpha$ integral too, and $\alpha$ compatible with the inclusions into Laurent series; a place specialisation $Psp$ and a prolongation datum $Rpd$ for $Psp$ and $\theta$, satisfying `TypeDichotomy` and `IsModel` for $\alpha$, $\theta \circ \alpha$, $\delta$; the condition $hwgen$ that $\theta$ computes the effect on places of composing a $\overline{\mathbb{Q}}$-point with the isomorphism $\mathfrak{X}.w$; and two compatibility conditions $hcompat$, $hcompat'$ identifying, for $\overline{\mathbb{Q}}$-points $y$ and closed points $P_0$ of the fibre curve model $\mathfrak{X}.\mathrm{Mfib}$ lying over the given $\kappa$-point via the $i$-th component map, the place of $P_0$ with `reduceFst` resp. `reduceSnd` of the place of $y$, and their Frobenius twists (summarised here). Finally let $Q$ be a place of `xHFunctionFieldBar M H` over $\overline{\mathbb{Q}}$ satisfying `IsStrictFst`, i.e. $\delta$ of the mod-$p$ Frobenius twist of $Psp.\mathrm{reduceFst}\,Q$ equals $Psp.\mathrm{reduceSnd}\,Q$ while $Psp.\mathrm{reduceFst}\,Q$ is not $\delta$-fixed; let $u$ be an $A$-valued section of the model over $\mathrm{Spec}\,\rho$ whose geometric point is the one corresponding to $Q$, $u_\kappa$ its reduction to the special fibre, a section of the fibre projection, and $P_0$ a closed point of $\mathfrak{X}.\mathrm{Mfib}$ mapping, under `efib` followed by the zeroth component map, to the closed point of $u_\kappa$, with place of $P_0$ equal to $Psp.\mathrm{reduceFst}\,Q$, and assume that closed point does not lie in the image of the first component map. Write $x_0$ for the image in $XO(\Gamma_M, \rho)$ of the closed point of $u_\kappa$ under the base-change map `bcMap`. The conclusion asserts: for every specialisation relation $hsp$ from the image of the generic point of $\mathfrak{X}.\mathrm{Meta}.C$ under `eeta` followed by the projection $prA$ to $x_0$, and with $\mathrm{emb}$ the resulting ring homomorphism from the stalk of $XO$ at $x_0$ to `xHFunctionFieldBar M H` obtained by composing `stalkSpecializes hsp`, the stalk maps of $prA$ and of `eeta` at the generic point, and $\mathfrak{X}.\mathrm{Meta}.\mathrm{ffEquiv}^{-1}$, every $f$ in `xHFunctionFieldBar M H` which lies in the integers of $Rpd.R_1$ and lies in the valuation subring of every place $W$ satisfying `IsStrictFst` with $Psp.\mathrm{reduceFst}\,W = Psp.\mathrm{reduceFst}\,Q$ lies in the range of $\mathrm{emb}$.
--
--   This is the Hartogs-type regularity statement on the Deligne–Rapoport model at a level exactly divisible by $p$: a function integral for the Gauss prolongation $R_1$ and pole-free at all strict places of the first kind reducing to a given smooth point of the special fibre is the germ of a section at that point. It is used by [`ModularCurve.XHDRModelAtP.exists_discParameter_ringHom_powerSeries_taylor_and_ord_residue_eq_of_isStrict`](thm.html#ModularCurve.XHDRModelAtP.exists_discParameter_ringHom_powerSeries_taylor_and_ord_residue_eq_of_isStrict), which produces a local parameter and a power series (Taylor) expansion with the prescribed order of the reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_mem_range_stalk_read_of_mem_integers_of_forall_isStrictFst_mem.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.mem_range_stalk_read_of_mem_integers_of_forall_isStrictFst_mem
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

    (Q : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hQ : Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ Q)
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hu : barPt A ≫ u.1 = ((𝔛.Meta).pointEquivPlace.symm Q).1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (huκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
    (huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (hP0 : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    (hP0Q : (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 = Psp.reduceFst α hα Q)
    (hsmooth : uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∉ Set.range (𝔛.comp A hA ρ hρ 1).base) :
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prA : XQ ⟶ XO (ΓM M H) hj ρ :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])
    letI bcA := bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl

    letI x₀ : ↥(XO (ΓM M H) hj ρ) := bcA.base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    ∀ (hsp : prA.base (𝔛.eeta.base (genericPoint (𝔛.Meta).C)) ⤳ x₀),
    letI emb : ↥((XO (ΓM M H) hj ρ).presheaf.stalk x₀) →+* ↥(xHFunctionFieldBar M H) :=
      (𝔛.Meta).ffEquiv.symm.toRingHom.comp
        ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp
          ((prA.stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp
            ((XO (ΓM M H) hj ρ).presheaf.stalkSpecializes hsp).hom))
    ∀ f : ↥(xHFunctionFieldBar M H), f ∈ Rpd.R₁.integers →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceFst α hα W = Psp.reduceFst α hα Q → f ∈ W.toValuationSubring) →
      f ∈ emb.range := by sorry
