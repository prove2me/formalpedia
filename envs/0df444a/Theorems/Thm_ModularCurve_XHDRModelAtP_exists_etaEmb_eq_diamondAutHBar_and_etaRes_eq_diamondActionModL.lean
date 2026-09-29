-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_etaEmb_eq_diamondAutHBar_and_etaRes_eq_diamondActionModL
-- name    : ModularCurve.XHDRModelAtP.exists_etaEmb_eq_diamondAutHBar_and_etaRes_eq_diamondActionModL
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/7bb6f4db-c3ab-5a4a-9129-c4bbed1896e1
-- title:
--   Diamond at e lifts to germs and reduces mod l
-- statement:
--   Fix a prime $p$ and $M \neq 0$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image under `ZMod.unitsMap` to $(\mathbb{Z}/(M/p))^\times$ is $1$, a valuation subring $Pl$ of $\overline{\mathbb{Q}}$ with $p$ in its nonunits and with algebraically closed residue field of characteristic $p$, and the hypothesis `hj` that the $q$-expansion `jqModC` of $j$ lies in the function field at level $\top$. Let $\mathfrak{X}$ be a model datum `XHDRModelAtP p M H hpM hj` (the proper flat integral normal model of $X_H$ over $R p$ together with its curve model `Meta` over $\overline{\mathbb{Q}}$ with function field `xHFunctionFieldBar M H`, the isomorphism `eeta` onto the geometric generic fibre, the Galois and $q$-expansion pinning conditions), and let $\rho : R p \to Pl$ factor the structural map to $\overline{\mathbb{Q}}$. Given a morphism $gA$ from `Meta.C` to the base change of `toBase` along $\mathrm{Spec}\,\rho$ whose two projections are those of `eeta` and of `Meta.toBase` followed by `barPt Pl`, a morphism $bc$ from the fibre over the residue map $\mathrm{residue} \circ \rho$ to the same base change compatible with both projections, and the hypothesis `hsp` that the $gA$-image of the generic point of `Meta.C` specialises to the image of the generic point of $(\mathfrak{X}.\mathrm{Mfib})$.C under `efib` followed by `comp … 0` followed by $bc$, write $\mathrm{emb}$ for the ring homomorphism from the stalk at that latter point to `xHFunctionFieldBar M H` obtained by specialisation along `hsp`, the stalk map of $gA$ at the generic point of `Meta.C`, and `Meta.ffEquiv.symm`, and $\mathrm{res}$ for the ring homomorphism from the same stalk to the function field `qExpFunctionFieldC` over the residue field of $Pl$ at level `ΓN p M H hpM` obtained from the stalk map of `efib ≫ comp … 0 ≫ bc` and `(𝔛.Mfib …).ffEquiv.symm`. Then, assuming there exists a monoid homomorphism from $\Gamma_0(M/p)$ to the algebra automorphisms of `qExpFunctionFieldC` over the residue field of $Pl$ at level [`CohCarrier.GammaH (M/p) (infSubgroup p M H hpM)`](def/CohCarrier_Level.html#L133) satisfying `IsDiamondPullbackModL`, for every unit $e \in (\mathbb{Z}/M)^\times$ and every germ $g$ in that stalk there is a germ $g'$ in the same stalk with $\mathrm{emb}(g') = \langle e \rangle(\mathrm{emb}(g))$, where $\langle e \rangle$ is `diamondAutHBar M H e`, and $\mathrm{res}(g') = \mathrm{diamondActionModL}(\gamma)(\mathrm{res}(g))$, where $\gamma$ is the chosen lift [`CuspForm.gammaLift (M/p)`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36) of the image of $e$ in $(\mathbb{Z}/(M/p))^\times$.
--
--   This is the compatibility of the diamond operator $\langle e \rangle$ with the two realisations of the function field of the model of $X_H(M)$ at $p$: its action on germs at the generic point of the component under consideration is simultaneously the diamond automorphism of the geometric characteristic-zero function field and the mod-$\mathfrak{l}$ diamond action at level $M/p$ on the reduction. It feeds the computation of reduced root functions under diamonds, via [`ModularCurve.reducedRootFunction_genOpH_dia_eq_smul_pow_mul_diamondActionModL_of_abelJacobiPin_tauFree`](thm.html#ModularCurve.reducedRootFunction_genOpH_dia_eq_smul_pow_mul_diamondActionModL_of_abelJacobiPin_tauFree).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_etaEmb_eq_diamondAutHBar_and_etaRes_eq_diamondActionModL.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_X1

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

theorem ModularCurve.XHDRModelAtP.exists_etaEmb_eq_diamondAutHBar_and_etaRes_eq_diamondActionModL

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

    (hsp : gA.base (genericPoint 𝔛.Meta.C) ⤳ (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)) :

    letI emb : ↥((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C))) →+* ↥(ModularCurve.xHFunctionFieldBar M H) :=
      𝔛.Meta.ffEquiv.symm.toRingHom.comp
        ((gA.stalkMap (genericPoint 𝔛.Meta.C)).hom.comp
          ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalkSpecializes hsp).hom)
    letI res : ↥((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C))) →+* ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM)) :=
      (𝔛.Mfib Pl hPl ρ hρ).ffEquiv.symm.toRingHom.comp ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).stalkMap (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)).hom
    haveI : NeZero (M / p) := ⟨Nat.pos_iff_ne_zero.mp (Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) hpM) (Fact.out : p.Prime).pos)⟩

    ∀ (hDPκ : ∃ ρκ : CongruenceSubgroup.Gamma0 (M / p) →*
          (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) ≃ₐ[IsLocalRing.ResidueField ↥Pl]
            ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))),
        IsDiamondPullbackModL (IsLocalRing.ResidueField ↥Pl) (M / p) (infSubgroup p M H hpM) ρκ)
      (e : (ZMod M)ˣ) (g : ↥((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)))),
      ∃ g' : ↥((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C))),
        emb g' = diamondAutHBar M H e (emb g) ∧
        res g' = diamondActionModL (IsLocalRing.ResidueField ↥Pl) (M / p) (infSubgroup p M H hpM)
            (CuspForm.gammaLift (M / p) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e)) (res g) := by sorry
