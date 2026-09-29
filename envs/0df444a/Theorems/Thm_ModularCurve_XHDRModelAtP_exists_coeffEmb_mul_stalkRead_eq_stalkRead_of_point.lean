-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_coeffEmb_mul_stalkRead_eq_stalkRead_of_point
-- name    : ModularCurve.XHDRModelAtP.exists_coeffEmb_mul_stalkRead_eq_stalkRead_of_point
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/6db0f803-054a-559c-8ff7-a77cc9080033
-- title:
--   Injective stalk reading of rational functions at a point
-- statement:
--   Fix a prime $p$ and a nonzero level $M$ with $p \mid M$ but $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image under the reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is trivial, with $M/p$ nonzero, and assume that the $q$-expansion `jqModC ℚ` lies in the field `qExpFunctionFieldC ℚ ⊤` generated over $\mathbb{Q}$ by ratios of integral $q$-expansions of modular forms of level one. Let $\mathfrak{X}$ be a Deligne–Rapoport bundle `XHDRModelAtP p M H hpM hj` for $X_H(M)$ at $p$, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ in which $p$ is a nonunit, with algebraically closed residue field of characteristic $p$, and let $\rho : R_p \to A$ be a ring map compatible with $R_p \to \overline{\mathbb{Q}}$. Let $O'$ be a discrete valuation domain with a map $\rho_{O'} : R_p \to O'$, an injective local homomorphism $\iota_{A'} : O' \to A$ with $\iota_{A'} \circ \rho_{O'} = \rho$, and a map $j_{O'} : O' \to \overline{\mathbb{Q}}$ with $j_{O'} \circ \rho_{O'} = (R_p \to \overline{\mathbb{Q}})$, $j_{O'}$ equal to $\iota_{A'}$ followed by $A \hookrightarrow \overline{\mathbb{Q}}$, and the residue maps of $A$ agreeing on $R_p$ along $\iota_{A'}$ and $\rho$. Let $x'$ be any point of $X' =$ `XO (ΓM M H) hj ρO'`, the base change of the model along $\operatorname{Spec} \rho_{O'}$, write $B$ for the stalk of $X'$ at $x'$ and $\sigma_B : O' \to B$ for the constants, i.e. $O' \cong \Gamma(\operatorname{Spec} O')$ followed by the pullback to global sections of $X'$ and the germ at $x'$. Let $X_{\overline{\mathbb{Q}}}$ be the base change along $R_p \to \overline{\mathbb{Q}}$ and $\mathrm{pr}_{J'} : X_{\overline{\mathbb{Q}}} \to X'$ the induced map over $\operatorname{Spec} j_{O'}$. Then for every specialisation of the image under $\mathrm{pr}_{J'} \circ \mathfrak{X}.eeta$ of the generic point of the curve $\mathfrak{X}.Meta.C$ to $x'$, the resulting map $\mathrm{emb} : B \to \overline{\mathbb{Q}} \cdot F(\Gamma_H(M))$ — specialisation of stalks, then the stalk maps of $\mathrm{pr}_{J'}$ and of $\mathfrak{X}.eeta$, then the inverse of the identification `ffEquiv` of the function field of $\mathfrak{X}.Meta.C$ with `xHFunctionFieldBar M H` — is injective, satisfies $\mathrm{emb} \circ \sigma_B = (\overline{\mathbb{Q}} \to \mathrm{xHFunctionFieldBar}\ M\ H) \circ j_{O'}$, and for every $a$ in the function field `qExpFunctionFieldC ℚ (ΓM M H)` there are $r, s \in B$ with $s \neq 0$ and $\mathrm{coeffEmb}(a) \cdot \mathrm{emb}(s) = \mathrm{emb}(r)$, where $\mathrm{coeffEmb}(a)$ is the coefficientwise image of $a$ under $\mathbb{Q} \to \overline{\mathbb{Q}}$, an element of `xHFunctionFieldBar M H`.
--
--   This is the point-generic form of the stalk-reading statement for the Deligne–Rapoport model of $X_H(M)$ over a coefficient discrete valuation ring: every rational function of $X_H(M)$ over $\mathbb{Q}$ becomes, after extension of coefficients to $\overline{\mathbb{Q}}$, a quotient of germs at an arbitrary point $x'$ of the model, the reading map being injective and restricting to $j_{O'}$ on constants. It feeds [`ModularCurve.XHDRModelAtP.exists_coeffRing_isIso_residueFieldMap_and_mul_stalkRead_eq`](thm.html#ModularCurve.XHDRModelAtP.exists_coeffRing_isIso_residueFieldMap_and_mul_stalkRead_eq), where the stalk is compared with a coefficient ring and its residue field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_coeffEmb_mul_stalkRead_eq_stalkRead_of_point.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
  ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_coeffEmb_mul_stalkRead_eq_stalkRead_of_point
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] (ρO' : R p →+* O')
    (ιA' : O' →+* ↥A) (hιA'inj : Function.Injective ιA') (hιA'loc : IsLocalHom ιA') (hιA'ρ : ιA'.comp ρO' = ρ)
    (jO' : O' →+* AlgebraicClosure ℚ) (hjO' : jO'.comp ρO' = algebraMap (R p) (AlgebraicClosure ℚ)) (hιA'j : A.subtype.comp ιA' = jO')
    (htoκ' : ((IsLocalRing.residue ↥A).comp ιA').comp ρO' = (IsLocalRing.residue ↥A).comp ρ)

    (x' : ↥(XO (ΓM M H) hj ρO')) :
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prJ' : XQ ⟶ XO (ΓM M H) hj ρO' :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO')) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO'])
    letI B := (XO (ΓM M H) hj ρO').presheaf.stalk x'
    letI σB : O' →+* ↥B := ((XO (ΓM M H) hj ρO').presheaf.germ ⊤ x' trivial).hom.comp
      (((XO.toBase (ΓM M H) hj ρO').appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O')).inv.hom)
    ∀ (hsp : prJ'.base (𝔛.eeta.base (genericPoint (𝔛.Meta).C)) ⤳ x'),
    letI emb : ↥B →+* ↥(xHFunctionFieldBar M H) := (𝔛.Meta).ffEquiv.symm.toRingHom.comp
      ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp
        ((prJ'.stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp
          ((XO (ΓM M H) hj ρO').presheaf.stalkSpecializes hsp).hom))
    Function.Injective emb ∧
    emb.comp σB = (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).comp jO' ∧
    ∀ a : ↥(qExpFunctionFieldC ℚ (ΓM M H)),
      ∃ r s : ↥B, s ≠ 0 ∧
        (⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (a : LaurentSeries ℚ),
            ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) a.2⟩ : ↥(xHFunctionFieldBar M H)) * emb s =
          emb r := by sorry
