-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_base_eq_closedPoint_and_forall_readA_mem_integers_and_isUnit_germ_iff
-- name    : ModularCurve.XHDRModelAtP.exists_base_eq_closedPoint_and_forall_readA_mem_integers_and_isUnit_germ_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/c05d53f9-002d-5efd-9d70-70abe8a6206f
-- title:
--   A centre for the prolongation R₁ on the model over A
-- statement:
--   Fix a prime $p$ and a non-zero $M$ with $p \mid M$ but $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit of $\mathbb{Z}/M$ whose image in $(\mathbb{Z}/(M/p))^\times$ under `ZMod.unitsMap` is $1$, with $M/p$ non-zero. Assume `hj`, that the Laurent series `jqModC ℚ` lies in the level-one $q$-expansion function field $\mathbb{Q}$-subfield `qExpFunctionFieldC ℚ ⊤`, and let $\mathfrak{X}$ be a term of `XHDRModelAtP p M H hpM hj`, so in particular a proper, flat, integral model `X p (ΓM M H) hj` over `Spec (R p)` together with a curve model `𝔛.Meta` over $\overline{\mathbb{Q}}$ with function field identified with $F :=$ `xHFunctionFieldBar M H` by `𝔛.Meta.ffEquiv`, and an isomorphism `𝔛.eeta` from `𝔛.Meta.C` onto the base change of the model to $\overline{\mathbb{Q}}$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, whose residue field is algebraically closed of characteristic $p$, and $\rho : R p \to A$ a ring homomorphism whose composition with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map $R p \to \overline{\mathbb{Q}}$. Let $\theta$ be a $\overline{\mathbb{Q}}$-algebra automorphism of $F$, let `Psp` be a place specialisation datum `JHPlaceSpecialization p M H hpM A`, and let `Rpd` be a prolongation datum for `Psp` and $\theta$, with first regular prolongation $R_1$ of $A$ to $F$ (a valuation subring `Rpd.R₁.integers` of $F$ with residue map onto the reduction field). Write $X_A :=$ `XO (ΓM M H) hj ρ` for the base change of the model along $\rho$, $X_{\overline{\mathbb{Q}}}$ for its base change to $\overline{\mathbb{Q}}$, and `prA` for the canonical morphism $X_{\overline{\mathbb{Q}}} \to X_A$ induced by $A \hookrightarrow \overline{\mathbb{Q}}$. The assertion is that there is a point $c$ of $X_A$ lying over the closed point of `Spec A` under `XO.toBase (ΓM M H) hj ρ` such that, for every open $V \subseteq X_A$ whose preimage in `𝔛.Meta.C` (along `𝔛.eeta` followed by `prA`) contains the generic point of `𝔛.Meta.C`, every section $g \in \Gamma(X_A, V)$ and every proof that $c \in V$, the element $\mathrm{read}_A(g) \in F$ obtained by restricting $g$ along `prA` and `𝔛.eeta`, taking the germ at that generic point, and transporting along `𝔛.Meta.ffEquiv.symm`, lies in `Rpd.R₁.integers`, and the germ of $g$ at $c$ is a unit of the stalk of $X_A$ at $c$ if and only if the $R_1$-residue of $\mathrm{read}_A(g)$ is non-zero.
--
--   This is the existence of a centre on the proper $A$-scheme $X_A$ for the valuation ring $R_1 \supseteq A$ of the function field of $X_A$, with the domination relation $R_1 \supseteq \mathcal{O}_{X_A,c}$ expressed on sections: membership in $R_1$ and the unit-versus-non-zero-residue equivalence, so that users need not work with stalks directly. It is used by [`ModularCurve.XHDRModelAtP.readA_mem_integers_and_residue_eq_restrict_comp_of_mem`](thm.html#ModularCurve.XHDRModelAtP.readA_mem_integers_and_residue_eq_restrict_comp_of_mem), in the identification of the reduction of $q$-expansions at level $M$ with sections on the special fibre of the Deligne–Rapoport model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_base_eq_closedPoint_and_forall_readA_mem_integers_and_isUnit_germ_iff.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_JHPlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
  ModularCurve.JZeroNeronObjectAtP MvPolynomial
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_base_eq_closedPoint_and_forall_readA_mem_integers_and_isUnit_germ_iff
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ) :
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prA : XQ ⟶ XO (ΓM M H) hj ρ :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])
    ∃ c : ↥(XO (ΓM M H) hj ρ), (XO.toBase (ΓM M H) hj ρ).base c = IsLocalRing.closedPoint ↥A ∧
      ∀ (V : (XO (ΓM M H) hj ρ).Opens) (hgenV : genericPoint (𝔛.Meta).C ∈ 𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ V))
        (g : Γ(XO (ΓM M H) hj ρ, V)) (hc : c ∈ V),
      letI readA : Γ(XO (ΓM M H) hj ρ, V) →+* ↥(xHFunctionFieldBar M H) :=
        (𝔛.Meta).ffEquiv.symm.toRingHom.comp
          (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ V)) (genericPoint (𝔛.Meta).C) hgenV).hom.comp
            ((𝔛.eeta.app (prA ⁻¹ᵁ V)).hom.comp (prA.app V).hom))
      ∃ h : readA g ∈ Rpd.R₁.integers,
        (IsUnit ((XO (ΓM M H) hj ρ).presheaf.germ V c hc g) ↔ Rpd.R₁.residue ⟨readA g, h⟩ ≠ 0) := by sorry
