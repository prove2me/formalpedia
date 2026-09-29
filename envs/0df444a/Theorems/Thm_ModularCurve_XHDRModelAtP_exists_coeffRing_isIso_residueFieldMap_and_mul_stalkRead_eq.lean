-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_coeffRing_isIso_residueFieldMap_and_mul_stalkRead_eq
-- name    : ModularCurve.XHDRModelAtP.exists_coeffRing_isIso_residueFieldMap_and_mul_stalkRead_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/f0a856a7-ff5e-5be1-9219-1f7099b6534e
-- title:
--   Coefficient descent to a DVR with rational special point
-- statement:
--   Fix a prime $p$ and a positive integer $M$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image under the reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is $1$, with $M/p$ nonzero, and assume $j$ has a $q$-expansion lying in `qExpFunctionFieldC ℚ ⊤`. Let $\mathfrak{X}$ be an `XHDRModelAtP p M H hpM hj` package: the two-chart integral model $X$ of the level-$\Gamma_H(M)$ function field over the base ring `R p`, with properness, flatness, integrality, normality of its affine sections, the corresponding data at level `ΓN p M H hpM`, and a curve model `𝔛.Meta` over $\overline{\mathbb{Q}}$ with function field `xHFunctionFieldBar M H` together with an isomorphism `𝔛.eeta` onto the base change of $X$ to $\overline{\mathbb{Q}}$ compatible with the structure morphisms and with the Galois action. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$, whose residue field $\kappa$ has characteristic $p$ and is algebraically closed, and let $\rho : R_p \to A$ satisfy $\iota_A \circ \rho =$ the structure map $R_p \to \overline{\mathbb{Q}}$. Let $u_\kappa : \operatorname{Spec} \kappa \to X \times_{\operatorname{Spec} R_p} \operatorname{Spec} \kappa$ be a section of the projection to $\operatorname{Spec} \kappa$, i.e. a $\kappa$-rational point of the geometric special fibre taken along $\mathrm{residue} \circ \rho$. Then for every $f$ in `xHFunctionFieldBar M H` there are a discrete valuation domain $O'$, a ring map $\rho_{O'} : R_p \to O'$, an injective local homomorphism $\iota_{A'} : O' \to A$ with $\iota_{A'} \circ \rho_{O'} = \rho$, a map $j_{O'} : O' \to \overline{\mathbb{Q}}$ with $j_{O'} \circ \rho_{O'}$ the structure map and $A \hookrightarrow \overline{\mathbb{Q}}$ composed with $\iota_{A'}$ equal to $j_{O'}$, and the induced compatibility of residue maps, such that the following holds. Write $X_{\overline{\mathbb{Q}}}$ for the base change of $X$ to $\overline{\mathbb{Q}}$, $\mathrm{pr}_{J'} : X_{\overline{\mathbb{Q}}} \to X_{O'}$ for the morphism to the base change $X_{O'}$ of $X$ along $\rho_{O'}$ induced by $j_{O'}$, $\mathrm{bc}'$ for the map from the fibre along $\mathrm{residue} \circ \iota_{A'} \circ \rho_{O'}$ to $X_{O'}$, $x'$ for the image under $\mathrm{bc}'$ of the image under $u_\kappa$ of the closed point of $\kappa$, and $B$ for the stalk of $X_{O'}$ at $x'$, equipped with the canonical map $\sigma_B : O' \to B$ coming from the germ at $x'$ of the structure morphism. The conclusion is that the image under $\mathrm{pr}_{J'}$ of the image under `𝔛.eeta` of the generic point of `𝔛.Meta.C` specialises to $x'$, and, with $\mathrm{emb} : B \to$ `xHFunctionFieldBar M H` the composite of the specialisation map $B \to$ (stalk at that generic image), the stalk maps of $\mathrm{pr}_{J'}$ and of `𝔛.eeta`, and the inverse of `𝔛.Meta.ffEquiv`, one has: $x'$ lies over the closed point of $O'$; the residue field map of $X_{O'} \to \operatorname{Spec} O'$ at $x'$ is an isomorphism; and there exist $r, s_0 \in B$ with $s_0 \neq 0$ and $f \cdot \mathrm{emb}(s_0) = \mathrm{emb}(r)$.
--
--   This is the coefficient-descent step with a rationality refinement: a single element of the geometric function field of $X_H(M)$ is realised as a fraction of germs on a model over a discrete valuation subring $O'$ of $A$, chosen so that the point under the given $\kappa$-rational point of the special fibre has residue field equal to that of $O'$. The rationality of that point is what is used downstream, in the results on membership of stalk-read functions in the integers for the two strict components of the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_coeffRing_isIso_residueFieldMap_and_mul_stalkRead_eq.lean

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

theorem ModularCurve.XHDRModelAtP.exists_coeffRing_isIso_residueFieldMap_and_mul_stalkRead_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    :
    ∀ f : ↥(xHFunctionFieldBar M H),
      ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O') (ρO' : R p →+* O')
        (ιA' : O' →+* ↥A) (_ : Function.Injective ιA') (_ : IsLocalHom ιA') (_ : ιA'.comp ρO' = ρ)
        (jO' : O' →+* AlgebraicClosure ℚ) (hjO' : jO'.comp ρO' = algebraMap (R p) (AlgebraicClosure ℚ)) (_ : A.subtype.comp ιA' = jO')
        (htoκ' : ((IsLocalRing.residue ↥A).comp ιA').comp ρO' = (IsLocalRing.residue ↥A).comp ρ),
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prJ' : XQ ⟶ XO (ΓM M H) hj ρO' :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO')) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO'])
    letI bc' := bcMap (ΓM M H) hj ρO' ((IsLocalRing.residue ↥A).comp ιA') htoκ'
    letI x' : ↥(XO (ΓM M H) hj ρO') := bc'.base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    letI B := (XO (ΓM M H) hj ρO').presheaf.stalk x'
    letI σB : O' →+* ↥B := ((XO (ΓM M H) hj ρO').presheaf.germ ⊤ x' trivial).hom.comp
      (((XO.toBase (ΓM M H) hj ρO').appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O')).inv.hom)
      ∃ (hsp : prJ'.base (𝔛.eeta.base (genericPoint (𝔛.Meta).C)) ⤳ x'),
      letI emb : ↥B →+* ↥(xHFunctionFieldBar M H) := (𝔛.Meta).ffEquiv.symm.toRingHom.comp
        ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp
          ((prJ'.stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp
            ((XO (ΓM M H) hj ρO').presheaf.stalkSpecializes hsp).hom))
      (XO.toBase (ΓM M H) hj ρO').base x' = IsLocalRing.closedPoint O' ∧
      IsIso ((XO.toBase (ΓM M H) hj ρO').residueFieldMap x') ∧
      ∃ r s₀ : ↥B, s₀ ≠ 0 ∧ f * emb s₀ = emb r := by sorry
