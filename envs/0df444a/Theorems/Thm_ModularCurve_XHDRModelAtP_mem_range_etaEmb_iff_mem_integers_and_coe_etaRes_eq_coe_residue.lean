-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_mem_range_etaEmb_iff_mem_integers_and_coe_etaRes_eq_coe_residue
-- name    : ModularCurve.XHDRModelAtP.mem_range_etaEmb_iff_mem_integers_and_coe_etaRes_eq_coe_residue
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/cf8ada3d-6241-5a1b-bf95-6094954333b8
-- title:
--   Germs at the Σ^∞ generic point form the Gauss ring
-- statement:
--   Fix a prime $p$ and $M$ nonzero with $p \mid M$ but $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image in $(\mathbb{Z}/(M/p))^\times$ is $1$, and a valuation subring $Pl$ of $\overline{\mathbb{Q}}$ with $p$ in its nonunits, whose residue field is algebraically closed of characteristic $p$. Assume $j$, given as `jqModC ℚ`, lies in `qExpFunctionFieldC ℚ ⊤`, let $\mathfrak{X}$ be a model datum `XHDRModelAtP p M H hpM hj`, and let $\rho : R p \to Pl$ be a ring homomorphism lifting the structure map $R p \to \overline{\mathbb{Q}}$. Further data: a morphism $gA$ from $\mathfrak{X}.\mathrm{Meta}.C$ to the base change of `toBase p (ΓM M H) hj` along $\operatorname{Spec}\rho$ agreeing with $\mathfrak{X}.\mathrm{eeta}$ on the first projection and with $\mathfrak{X}.\mathrm{Meta}.\mathrm{toBase}$ followed by `barPt Pl` on the second; a morphism $bc$ from the fibre over `residue ∘ ρ` to that base change, commuting with both projections (the second up to $\operatorname{Spec}$ of the residue map); and a regular prolongation $Rg$ of $Pl$ to $\overline{\mathbb{Q}}\cdot F$, where $F$ is `qExpFunctionFieldC ℚ (GammaH M H)`, with residue field `qExpFunctionFieldC (ResidueField Pl) (GammaH M H)`, pinned to be the Gauss prolongation: $f$ lies in `Rg.integers` exactly when $f \cdot y = x$ for Laurent series $x, y$ over $Pl$ with $y$ having nonzero reduction; every Laurent series over $Pl$ lying in $\overline{\mathbb{Q}}\cdot F$ is integral with residue its coefficientwise reduction; and $\mathrm{res}(f)\cdot \bar y = \bar x$ for any such witnesses. Finally assume the image under $gA$ of the generic point of $\mathfrak{X}.\mathrm{Meta}.C$ specialises to the image of the generic point of $(\mathfrak{X}.\mathrm{Mfib}\,Pl\,hPl\,\rho\,h\rho).C$ under $\mathfrak{X}.\mathrm{efib} \ggg \mathfrak{X}.\mathrm{comp}\,0 \ggg bc$. Let $\mathrm{emb}$ be the ring homomorphism from the stalk of the base change at that latter point to `xHFunctionFieldBar M H` obtained by specialisation of stalks, the stalk map of $gA$ at the generic point, and $\mathfrak{X}.\mathrm{Meta}.\mathrm{ffEquiv}^{-1}$; let $\mathrm{res}$ be the analogous homomorphism from the same stalk to `qExpFunctionFieldC (ResidueField Pl) (ΓN p M H hpM)` built from the stalk map of $\mathfrak{X}.\mathrm{efib} \ggg \mathfrak{X}.\mathrm{comp}\,0 \ggg bc$ and $(\mathfrak{X}.\mathrm{Mfib}\,\dots).\mathrm{ffEquiv}^{-1}$. The conclusion is twofold: an element of `xHFunctionFieldBar M H` lies in the range of $\mathrm{emb}$ if and only if, viewed in $\overline{\mathbb{Q}}\cdot F$, it lies in `Rg.integers`; and for every germ $g$ in the stalk with $\mathrm{emb}\,g$ integral, the Laurent series underlying $\mathrm{res}\,g$ equals the Laurent series underlying `Rg.residue ⟨emb g, hg⟩`.
--
--   This identifies the local ring at the generic point of the $\Sigma^\infty$ component of the Deligne–Rapoport-style model with the Gauss valuation ring of $q$-expansions over $Pl$, and identifies restriction of germs to that component with coefficientwise Gauss reduction of $q$-expansions. It is the bridge used when reading the reduction of modular functions off their $q$-expansions, and is invoked in the computation of the reduced root function and its behaviour under the diamond operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_mem_range_etaEmb_iff_mem_integers_and_coe_etaRes_eq_coe_residue.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra IsLocalRing AlgebraicCurve
  ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
set_option maxHeartbeats 800000 in
open Classical in
open ModularCurve in
open Classical in
open ModularCurve in

theorem ModularCurve.XHDRModelAtP.mem_range_etaEmb_iff_mem_integers_and_coe_etaRes_eq_coe_residue

    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt Pl)
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)))

    (Rg : AlgebraicCurve.RegularProlongation Pl ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H)))
    (hRg₁ : ∀ f : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))), f ∈ Rg.integers ↔
        ∃ x y : LaurentSeries ↥Pl, ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y ≠ 0 ∧
          (f : LaurentSeries (AlgebraicClosure ℚ)) * ModularCurve.coeffMap Pl.subtype y = ModularCurve.coeffMap Pl.subtype x)
    (hRg₂ : ∀ (y : LaurentSeries ↥Pl) (hy : ModularCurve.coeffMap Pl.subtype y ∈ ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))),
        ∃ hO : (⟨ModularCurve.coeffMap Pl.subtype y, hy⟩ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ∈ Rg.integers,
          ((Rg.residue ⟨_, hO⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) = ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y)
    (hRg₃ : ∀ (f : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) (hf : f ∈ Rg.integers) (x y : LaurentSeries ↥Pl),
        ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y ≠ 0 →
        (f : LaurentSeries (AlgebraicClosure ℚ)) * ModularCurve.coeffMap Pl.subtype y = ModularCurve.coeffMap Pl.subtype x →
        ((Rg.residue ⟨f, hf⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) * ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y =
          ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) x)

    (hsp : gA.base (genericPoint 𝔛.Meta.C) ⤳ (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)) :

    letI emb : ↥((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C))) →+* ↥(ModularCurve.xHFunctionFieldBar M H) :=
      𝔛.Meta.ffEquiv.symm.toRingHom.comp
        ((gA.stalkMap (genericPoint 𝔛.Meta.C)).hom.comp
          ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalkSpecializes hsp).hom)
    letI res : ↥((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C))) →+* ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM)) :=
      (𝔛.Mfib Pl hPl ρ hρ).ffEquiv.symm.toRingHom.comp ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).stalkMap (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)).hom
    (∀ f : ↥(ModularCurve.xHFunctionFieldBar M H), f ∈ emb.range ↔ (f : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ∈ Rg.integers) ∧
    (∀ (g : ↥((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)))) (hg : (emb g : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ∈ Rg.integers),
      ((res g : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) =
        ((Rg.residue ⟨emb g, hg⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl))) := by sorry
