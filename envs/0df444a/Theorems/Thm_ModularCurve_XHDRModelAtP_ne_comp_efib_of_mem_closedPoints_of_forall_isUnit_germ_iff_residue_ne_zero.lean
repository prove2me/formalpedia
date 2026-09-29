-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_ne_comp_efib_of_mem_closedPoints_of_forall_isUnit_germ_iff_residue_ne_zero
-- name    : ModularCurve.XHDRModelAtP.ne_comp_efib_of_mem_closedPoints_of_forall_isUnit_germ_iff_residue_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/9bcd368a-9370-5ad4-b042-e626c6e77c60
-- title:
--   Gauss-dominated closed-fibre point is not a closed point
-- statement:
--   Fix a prime $p$ and a nonzero level $M$ with $p \mid M$ but $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that reduces to $1$ in $(\mathbb{Z}/(M/p))^\times$, with $M/p$ nonzero, and assume the $q$-expansion `jqModC ℚ` of $j$ lies in the field `qExpFunctionFieldC ℚ ⊤`. Let $\mathfrak{X}$ be a model package `XHDRModelAtP p M H hpM hj` for $X_H(M)$ over the base ring `R p`, with geometric curve model `𝔛.Meta` having function field `xHFunctionFieldBar M H`, and isomorphism `𝔛.eeta` onto the base change of `toBase p (ΓM M H) hj` along `R p → AlgebraicClosure ℚ`. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$, whose residue field is algebraically closed of characteristic $p$, and let $\rho : \mathrm{R}\,p \to A$ be a ring homomorphism whose composite with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map. Let $\theta$ be an $\overline{\mathbb{Q}}$-algebra automorphism of `xHFunctionFieldBar M H`, let `Psp` be place-specialisation data `JHPlaceSpecialization p M H hpM A`, and let `Rpd` be a prolongation datum for `Psp` and $\theta$, consisting of regular prolongations $R_1, R_2$ of $A$ to `xHFunctionFieldBar M H` with residue field `Fbar`, the first compatible with $q$-expansion reduction and the second obtained from it through $\theta$. Write $X_A$ for `XO (ΓM M H) hj ρ`, the base change of the model along $\rho$, and $X_{\overline{\mathbb{Q}}}$ for its base change along $\mathrm{R}\,p \to \overline{\mathbb{Q}}$, with `prA` the canonical morphism $X_{\overline{\mathbb{Q}}} \to X_A$ induced by $A \hookrightarrow \overline{\mathbb{Q}}$. The assertion is: for every point $c$ of $X_A$ mapping to the closed point of $\operatorname{Spec} A$ under `XO.toBase`, if for every open $V \subseteq X_A$ such that the generic point of `(𝔛.Meta).C` lies in the preimage of $V$ under `𝔛.eeta` followed by `prA`, every $g \in \Gamma(X_A, V)$ and every $c \in V$, the element `readA g` of `xHFunctionFieldBar M H` obtained by pulling $g$ back along `prA` and `𝔛.eeta`, taking the germ at that generic point and transporting it through `(𝔛.Meta).ffEquiv.symm`, lies in $R_1$ and satisfies: the germ of $g$ at $c$ is a unit if and only if the $R_1$-residue of `readA g` is nonzero — then for each $i \in \{0,1\}$ and each closed point $w$ of the curve `(𝔛.Mfib A hA ρ hρ).C`, $c$ is different from the image of $w$ under `𝔛.efib A hA ρ hρ` followed by `𝔛.comp A hA ρ hρ i` followed by the base-change morphism `bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl` from the special fibre over the residue field of $A$ to $X_A$.
--
--   This is one half of the localisation of a point of the special fibre of the Deligne–Rapoport model $X_H(M)_A$ that is dominated, on sections, by the Gauss prolongation $R_1$: such a point cannot be the image of a closed point of the geometric special-fibre curve along either of the two branch morphisms. It is used by [`ModularCurve.XHDRModelAtP.eq_xiInf_of_base_eq_closedPoint_of_forall_isUnit_germ_iff_residue_ne_zero`](thm.html#ModularCurve.XHDRModelAtP.eq_xiInf_of_base_eq_closedPoint_of_forall_isUnit_germ_iff_residue_ne_zero), which concludes that the dominated point is the generic point of the component attached to the $\infty$-end.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_ne_comp_efib_of_mem_closedPoints_of_forall_isUnit_germ_iff_residue_ne_zero.lean

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

theorem ModularCurve.XHDRModelAtP.ne_comp_efib_of_mem_closedPoints_of_forall_isUnit_germ_iff_residue_ne_zero
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
    ∀ c : ↥(XO (ΓM M H) hj ρ), (XO.toBase (ΓM M H) hj ρ).base c = IsLocalRing.closedPoint ↥A →
      (∀ (V : (XO (ΓM M H) hj ρ).Opens) (hgenV : genericPoint (𝔛.Meta).C ∈ 𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ V))
        (g : Γ(XO (ΓM M H) hj ρ, V)) (hc : c ∈ V),
        letI readA : Γ(XO (ΓM M H) hj ρ, V) →+* ↥(xHFunctionFieldBar M H) :=
          (𝔛.Meta).ffEquiv.symm.toRingHom.comp
            (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ V)) (genericPoint (𝔛.Meta).C) hgenV).hom.comp
              ((𝔛.eeta.app (prA ⁻¹ᵁ V)).hom.comp (prA.app V).hom))
        ∃ h : readA g ∈ Rpd.R₁.integers,
          (IsUnit ((XO (ΓM M H) hj ρ).presheaf.germ V c hc g) ↔ Rpd.R₁.residue ⟨readA g, h⟩ ≠ 0)) →
      ∀ (i : Fin 2) (w : ↥(𝔛.Mfib A hA ρ hρ).C), w ∈ closedPoints (𝔛.Mfib A hA ρ hρ).C →
        c ≠ (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).base w := by sorry
