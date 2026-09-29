-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_injective_etaEmb_and_exists_valuationSubring_range_eq_rankOne_and_const
-- name    : ModularCurve.XHDRModelAtP.injective_etaEmb_and_exists_valuationSubring_range_eq_rankOne_and_const
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/70d33263-ccf2-5659-ba4b-09e3e31d11ec
-- title:
--   Generic-point stalk of the model: a maximal proper valuation subring
-- statement:
--   Fix a prime $p$ and $M>0$ with $p \mid M$ and $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image under the reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is $1$. Let $Pl$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $Pl$, whose residue field is algebraically closed of characteristic $p$; let $hj$ record that $jqModC\,\mathbb{Q}$ lies in `qExpFunctionFieldC ℚ ⊤`, and let $\mathfrak{X}$ be a term of [`ModularCurve.XHDRModelAtP p M H hpM hj`](def/ModularCurve_XHDRModelAtP.html#L81), so in particular the two-chart integral model `X p (ΓM M H) hj` over $R\,p = \mathbb{Z}_{(p)}$ is proper, flat, integral and normal, and comes with a curve model $\mathfrak{X}.\mathrm{Meta}$ over $\overline{\mathbb{Q}}$ with function field `xHFunctionFieldBar M H` and an isomorphism $\mathfrak{X}.\mathrm{eeta}$ onto the geometric generic fibre. Let $\rho : R\,p \to Pl$ lift the structure map of $\overline{\mathbb{Q}}$, let $gA$ be a morphism from $\mathfrak{X}.\mathrm{Meta}.C$ to the base change $\mathfrak{X}_{Pl}$ along $\rho$ agreeing with $\mathfrak{X}.\mathrm{eeta}$ on the first projection and with $\mathfrak{X}.\mathrm{Meta}.\mathrm{toBase}$ followed by $\mathrm{Spec}$ of the inclusion $Pl \hookrightarrow \overline{\mathbb{Q}}$ on the second, and let $bc$ be a morphism from the fibre of the model over the residue field of $Pl$ (the pullback along $\mathrm{residue} \circ \rho$) to $\mathfrak{X}_{Pl}$, compatible with both projections. Write $\eta$ for the image, under $\mathfrak{X}.\mathrm{efib}\ Pl\ hPl\ \rho\ h\rho$ followed by $\mathfrak{X}.\mathrm{comp}\ Pl\ hPl\ \rho\ h\rho\ 0$ followed by $bc$, of the generic point of the curve $(\mathfrak{X}.\mathrm{Mfib}\ Pl\ hPl\ \rho\ h\rho).C$, and assume that the image of the generic point of $\mathfrak{X}.\mathrm{Meta}.C$ under $gA$ specialises to $\eta$. Two ring homomorphisms out of the stalk of $\mathfrak{X}_{Pl}$ at $\eta$ are formed: $\mathrm{emb}$, the specialisation map to the stalk at $gA$ of the generic point, followed by the stalk map of $gA$ and by $\mathfrak{X}.\mathrm{Meta}.\mathrm{ffEquiv}^{-1}$, landing in `xHFunctionFieldBar M H`; and $\mathrm{res}$, the stalk map of the above composite at the generic point of $(\mathfrak{X}.\mathrm{Mfib}\ \ldots).C$ followed by that model's $\mathrm{ffEquiv}^{-1}$, landing in `qExpFunctionFieldC (ResidueField Pl) (ΓN p M H hpM)`. The assertion is threefold: $\mathrm{emb}$ is injective; its range is the subring of a valuation subring $V$ of `xHFunctionFieldBar M H` with $V \neq \top$ and with no valuation subring strictly between $V$ and the whole field (every $V' \ge V$ equals $V$ or $\top$); and for every $a \in Pl$, the germ at $\eta$ of the global section obtained from $a$ via the second projection is sent by $\mathrm{emb}$ to the image of $a$ in `xHFunctionFieldBar M H` under the structure map from $\overline{\mathbb{Q}}$, and by $\mathrm{res}$ to the image of the residue class of $a$ under the structure map from the residue field of $Pl$.
--
--   This identifies the local ring of the normal model $\mathfrak{X}$ of $X_H(M)$, base changed to the valuation ring $Pl$, at the generic point of the distinguished component of the special fibre, as a valuation subring of $\overline{\mathbb{Q}} \cdot F_H(M)$ that is maximal among proper valuation subrings, together with the compatible reading of constants on the generic fibre and on that component. It feeds the characterisation of the range of $\mathrm{emb}$ in terms of a regular prolongation and the later computation of reduced root functions in the Deligne–Rapoport fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_injective_etaEmb_and_exists_valuationSubring_range_eq_rankOne_and_const.lean

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

theorem ModularCurve.XHDRModelAtP.injective_etaEmb_and_exists_valuationSubring_range_eq_rankOne_and_const

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
    Function.Injective emb ∧
    (∃ V : ValuationSubring ↥(ModularCurve.xHFunctionFieldBar M H), emb.range = V.toSubring ∧ V ≠ ⊤ ∧
      ∀ V' : ValuationSubring ↥(ModularCurve.xHFunctionFieldBar M H), V ≤ V' → V' = V ∨ V' = ⊤) ∧
    (∀ a : ↥Pl,
      emb ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.germ ⊤ ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)) trivial
        ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥Pl)).inv a))) =
        algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ) ∧
      res ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.germ ⊤ ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)) trivial
        ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥Pl)).inv a))) =
        algebraMap (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM)) (IsLocalRing.residue ↥Pl a)) := by sorry
