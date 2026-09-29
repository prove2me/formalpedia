-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_notMem_span_and_mul_stalkRead_eq_of_mem_integers_of_isIso_residueFieldMap_of_not_mem_range_comp_one
-- name    : ModularCurve.XHDRModelAtP.exists_notMem_span_and_mul_stalkRead_eq_of_mem_integers_of_isIso_residueFieldMap_of_not_mem_range_comp_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/41335623-d51e-5d76-8282-25c954e5473f
-- title:
--   Denominators outside varpi' for Gauss-integral functions
-- statement:
--   Fix a prime $p$ and $M \neq 0$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that reduces to $1$ in $(\mathbb{Z}/(M/p))^\times$, with $M/p \neq 0$, and assume $j$ lies in the $q$-expansion function field at full level, as witnessed by `hj`. Let $\mathfrak{X}$ be a model package `XHDRModelAtP p M H hpM hj` for $X_H$ over $R p$, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, with algebraically closed residue field $\kappa$ of characteristic $p$, and let $\rho : R p \to A$ lift the structure map $R p \to \overline{\mathbb{Q}}$. Let $\theta$ be a $\overline{\mathbb{Q}}$-algebra automorphism of $F =$ `xHFunctionFieldBar M H`, let `Psp` be a place specialization datum `JHPlaceSpecialization p M H hpM A` and `Rpd` a prolongation datum for `Psp` and $\theta$, whose first component is a regular prolongation $R_1$ of $A$ to $F$. The hypothesis `hwgen` requires that whenever two $\overline{\mathbb{Q}}$-rational sections $y, y'$ of $\mathfrak{X}.\mathrm{Meta}.C$ over the base satisfy that $y'$ followed by `𝔛.eeta`, the first projection and $\mathfrak{X}.w$ agrees with $y$ followed by `𝔛.eeta` and the first projection, the associated places satisfy $\mathrm{pointEquivPlace}\,y' = \mathrm{ofAlgAut}(\theta) \cdot \mathrm{pointEquivPlace}\,y$. Further let $O'$ be a discrete valuation domain with uniformiser $\varpi'$, equipped with $\rho_{O'} : R p \to O'$, an injective local homomorphism $\iota_{A'} : O' \to A$ with $\iota_{A'} \circ \rho_{O'} = \rho$, a map $j_{O'} : O' \to \overline{\mathbb{Q}}$ compatible with the structure maps and with $\iota_{A'}$, and the corresponding compatibility of residue maps. Let $u_\kappa$ be a section of the geometric special fibre over $\kappa$ (a $\kappa$-point of `fibre` for the residue map $R p \to \kappa$) whose closed point does not lie in the image of $(\mathfrak{X}.\mathrm{comp}\ A\ hA\ \rho\ h\rho\ 1).\mathrm{base}$. Write $XQ$ for the geometric generic fibre, $prJ'$ for the induced morphism $XQ \to$ `XO (ΓM M H) hj ρO'` coming from $j_{O'}$, $x'$ for the image of the closed point of $u_\kappa$ in `XO (ΓM M H) hj ρO'` under the base-change map, $B$ for the stalk there, and $\sigma_B : O' \to B$ for the structure map via global sections. Assume the residue field map of `XO.toBase` at $x'$ is an isomorphism, and let `hsp` witness that the image under $prJ'$ of the generic point of $\mathfrak{X}.\mathrm{Meta}.C$ specialises to $x'$; let $\mathrm{emb} : B \to F$ be the composite of the specialisation map on stalks, the stalk maps of $prJ'$ and of `𝔛.eeta`, and the inverse of $\mathfrak{X}.\mathrm{Meta}.\mathrm{ffEquiv}$. Then for every $x \in F$ lying in the valuation subring $R_1.\mathrm{integers}$ and admitting some representation $x \cdot \mathrm{emb}(s_0) = \mathrm{emb}(r_0)$ with $r_0, s_0 \in B$ and $s_0 \neq 0$, there exist $r, s \in B$ with $s \notin (\sigma_B \varpi')B$ and $x \cdot \mathrm{emb}(s) = \mathrm{emb}(r)$.
--
--   This is the step identifying the localisation of the stalk $B$ at the vertical height-one prime $\varpi' B$ with the trace on the fraction field of the Gauss valuation ring $R_1$: an element of $F$ which is integral for the Gauss prolongation and is a quotient of germs at all can be written with denominator a unit at the vertical prime, provided the chosen $\kappa$-point of the special fibre avoids the component indexed by $1$ and is rational over the residue field of $O'$. It is used by [`ModularCurve.XHDRModelAtP.mem_range_stalk_read_of_mem_integers_of_forall_isStrictFst_mem`](thm.html#ModularCurve.XHDRModelAtP.mem_range_stalk_read_of_mem_integers_of_forall_isStrictFst_mem), in the identification of germs of the Deligne–Rapoport model at points of the special fibre with functions integral for the prolongations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_notMem_span_and_mul_stalkRead_eq_of_mem_integers_of_isIso_residueFieldMap_of_not_mem_range_comp_one.lean

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

theorem ModularCurve.XHDRModelAtP.exists_notMem_span_and_mul_stalkRead_eq_of_mem_integers_of_isIso_residueFieldMap_of_not_mem_range_comp_one
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)

    (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] (ρO' : R p →+* O')
    (ιA' : O' →+* ↥A) (hιA'inj : Function.Injective ιA') (hιA'loc : IsLocalHom ιA') (hιA'ρ : ιA'.comp ρO' = ρ)
    (jO' : O' →+* AlgebraicClosure ℚ) (hjO' : jO'.comp ρO' = algebraMap (R p) (AlgebraicClosure ℚ)) (hιA'j : A.subtype.comp ιA' = jO')
    (htoκ' : ((IsLocalRing.residue ↥A).comp ιA').comp ρO' = (IsLocalRing.residue ↥A).comp ρ)
    (ϖ' : O') (hϖ' : IsLocalRing.maximalIdeal O' = Ideal.span {ϖ'})

    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (hsm : uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∉ Set.range (𝔛.comp A hA ρ hρ 1).base) :
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prJ' : XQ ⟶ XO (ΓM M H) hj ρO' :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO')) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO'])
    letI bc' := bcMap (ΓM M H) hj ρO' ((IsLocalRing.residue ↥A).comp ιA') htoκ'
    letI x' : ↥(XO (ΓM M H) hj ρO') := bc'.base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    letI B := (XO (ΓM M H) hj ρO').presheaf.stalk x'
    letI σB : O' →+* ↥B := ((XO (ΓM M H) hj ρO').presheaf.germ ⊤ x' trivial).hom.comp
      (((XO.toBase (ΓM M H) hj ρO').appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O')).inv.hom)

    IsIso ((XO.toBase (ΓM M H) hj ρO').residueFieldMap x') →
    ∀ (hsp : prJ'.base (𝔛.eeta.base (genericPoint (𝔛.Meta).C)) ⤳ x'),
    letI emb : ↥B →+* ↥(xHFunctionFieldBar M H) := (𝔛.Meta).ffEquiv.symm.toRingHom.comp
      ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp
        ((prJ'.stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp
          ((XO (ΓM M H) hj ρO').presheaf.stalkSpecializes hsp).hom))
    ∀ x : ↥(xHFunctionFieldBar M H), x ∈ Rpd.R₁.integers → (∃ r₀ s₀ : ↥B, s₀ ≠ 0 ∧ x * emb s₀ = emb r₀) →
      ∃ r s : ↥B, s ∉ Ideal.span {σB ϖ'} ∧ x * emb s = emb r := by sorry
