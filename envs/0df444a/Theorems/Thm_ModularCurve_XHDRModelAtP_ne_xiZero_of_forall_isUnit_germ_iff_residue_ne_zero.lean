-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_ne_xiZero_of_forall_isUnit_germ_iff_residue_ne_zero
-- name    : ModularCurve.XHDRModelAtP.ne_xiZero_of_forall_isUnit_germ_iff_residue_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/9265a70f-56d5-5422-8a26-6fd66397ba36
-- title:
--   A point dominated by R₁ is not ξ₀
-- statement:
--   Fix a prime $p$ and a nonzero level $M$ with $p \mid M$ but $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that reduces to $1$ in $(\mathbb{Z}/(M/p))^\times$, and the hypothesis `hj` that the $q$-expansion `jqModC ℚ` of $j$ lies in the field `qExpFunctionFieldC ℚ ⊤` generated over $\mathbb{Q}$ by the integral form ratios for $SL(2,\mathbb{Z})$. Let $\mathfrak{X}$ be a model package `XHDRModelAtP p M H hpM hj` for $X_H(M)$ over `R p`, carrying in particular a curve model `𝔛.Meta` of $\overline{F}_M =$ `xHFunctionFieldBar M H` over $\overline{\mathbb{Q}}$ together with an isomorphism `𝔛.eeta` onto the base change of `toBase p (ΓM M H) hj` to $\overline{\mathbb{Q}}$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$ and with algebraically closed residue field of characteristic $p$, and let $\rho :$ `R p` $\to A$ be a ring homomorphism whose composite with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map. Let $\theta$ be a $\overline{\mathbb{Q}}$-algebra automorphism of $\overline{F}_M$, let `Psp` be a place-specialisation datum `JHPlaceSpecialization p M H hpM A`, and let `Rpd` be a prolongation datum for `Psp` and $\theta$, providing in particular a regular prolongation `Rpd.R₁` of $A$ to $\overline{F}_M$, with valuation subring `Rpd.R₁.integers` and residue homomorphism `Rpd.R₁.residue` to the reduced function field. Write $X_A =$ `XO (ΓM M H) hj ρ` for the base change of the model along $\rho$, $X_{\overline{\mathbb{Q}}}$ for its base change to $\overline{\mathbb{Q}}$, and `prA` for the canonical morphism $X_{\overline{\mathbb{Q}}} \to X_A$ induced by $A \hookrightarrow \overline{\mathbb{Q}}$. The assertion is: for every point $c$ of $X_A$ lying over the closed point of $\operatorname{Spec} A$, if for every open $V \subseteq X_A$ whose preimage under `prA` followed by `𝔛.eeta` contains the generic point of `𝔛.Meta.C`, every section $g \in \Gamma(X_A, V)$ and every witness $c \in V$, the generic reading of $g$ in $\overline{F}_M$ — obtained by pulling $g$ back along `prA` and `𝔛.eeta`, taking the germ at the generic point of `𝔛.Meta.C`, and transporting along `𝔛.Meta.ffEquiv.symm` — lies in `Rpd.R₁.integers` and satisfies: the germ of $g$ at $c$ is a unit if and only if the `Rpd.R₁`-residue of that reading is nonzero, then $c$ is not the point `𝔛.ξzero A hA ρ hρ ρ (IsLocalRing.residue ↥A) rfl` of $X_A$.
--
--   This is the non-degeneracy half of the identification of the centre of the Gauss prolongation on the special fibre of the Deligne–Rapoport style model of $X_H(M)$ at $p$: a point of the special fibre whose local ring is dominated, section by section, by the Gauss ring $\mathrm{R}_1$ cannot be the distinguished point $\xi_0$ attached to the $0$-branch. It is used by [`ModularCurve.XHDRModelAtP.eq_xiInf_of_base_eq_closedPoint_of_forall_isUnit_germ_iff_residue_ne_zero`](thm.html#ModularCurve.XHDRModelAtP.eq_xiInf_of_base_eq_closedPoint_of_forall_isUnit_germ_iff_residue_ne_zero), which concludes that such a point must instead be $\xi_\infty$; the discriminating input is the Frobenius twist $q \mapsto q^p$ in the reading of level-$(M/p)$ chart functions along the $0$-branch, recorded by [`ModularCurve.qExpFrobeniusModL_eq_inv_qExpArithFrobC_smul_pow`](thm.html#ModularCurve.qExpFrobeniusModL_eq_inv_qExpArithFrobC_smul_pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_ne_xiZero_of_forall_isUnit_germ_iff_residue_ne_zero.lean

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

theorem ModularCurve.XHDRModelAtP.ne_xiZero_of_forall_isUnit_germ_iff_residue_ne_zero
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
      c ≠ 𝔛.ξzero A hA ρ hρ ρ (IsLocalRing.residue ↥A) rfl := by sorry
