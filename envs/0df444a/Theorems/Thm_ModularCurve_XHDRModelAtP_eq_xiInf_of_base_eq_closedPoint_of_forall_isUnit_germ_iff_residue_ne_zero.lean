-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_eq_xiInf_of_base_eq_closedPoint_of_forall_isUnit_germ_iff_residue_ne_zero
-- name    : ModularCurve.XHDRModelAtP.eq_xiInf_of_base_eq_closedPoint_of_forall_isUnit_germ_iff_residue_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/8a28a196-07d7-557c-b684-bac5c509d742
-- title:
--   A point dominated by R₁ equals ξ_∞
-- statement:
--   Fix a prime $p$ and $M \neq 0$ with $p \mid M$ but $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image under `ZMod.unitsMap` for $M/p \mid M$ is $1$, with $M/p \neq 0$; assume `jqModC ℚ` lies in the $q$-expansion function field `qExpFunctionFieldC ℚ ⊤`, and let $\mathfrak{X}$ be a package `XHDRModelAtP p M H hpM hj`. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$, whose residue field has characteristic $p$ and is algebraically closed, and let $\rho : R_p \to A$ be a ring homomorphism whose composite with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map $R_p \to \overline{\mathbb{Q}}$. Let $\theta$ be an $\overline{\mathbb{Q}}$-algebra automorphism of the intermediate field `xHFunctionFieldBar M H` of $\overline{\mathbb{Q}}((q))$, let `Psp` be a `JHPlaceSpecialization p M H hpM A` and `Rpd` a prolongation datum for `Psp` and $\theta$, so that `Rpd.R₁` provides a valuation subring `Rpd.R₁.integers` of `xHFunctionFieldBar M H` together with its surjective residue map onto the reduction field, with kernel the maximal ideal. Write $X_{\overline{\mathbb{Q}}}$ for the base change of the two-chart integral model `toBase p (ΓM M H) hj` along $R_p \to \overline{\mathbb{Q}}$, and `prA` for the induced morphism $X_{\overline{\mathbb{Q}}} \to$ `XO (ΓM M H) hj ρ` given by the identity on the model and $\operatorname{Spec}$ of $A \hookrightarrow \overline{\mathbb{Q}}$ on the base. Then for every point $c$ of `XO (ΓM M H) hj ρ` lying over the closed point of $\operatorname{Spec} A$ the following holds: if for every open $V$ whose preimage under `prA` followed by $\mathfrak{X}.\mathrm{eeta}$ contains the generic point of $\mathfrak{X}.\mathrm{Meta}.C$, every section $g \in \Gamma(V)$ and every proof that $c \in V$, the element `readA g` of `xHFunctionFieldBar M H` — obtained by pulling $g$ back along `prA` and $\mathfrak{X}.\mathrm{eeta}$, taking its germ at the generic point of $\mathfrak{X}.\mathrm{Meta}.C$ and transporting along $\mathfrak{X}.\mathrm{Meta}.\mathrm{ffEquiv}^{-1}$ — lies in `Rpd.R₁.integers` and satisfies: the germ of $g$ at $c$ is a unit if and only if the `R₁`-residue of `readA g` is non-zero, then $c$ equals $\mathfrak{X}.\xi_{\inf}$ for the data $A$, $\rho$ and the residue map of $A$.
--
--   This is the $q$-expansion principle in valuation-theoretic form for the Deligne–Rapoport model of $X_H(M)$ at a prime exactly dividing the level: the Gauss-type valuation recorded by the first prolongation $R_1$ is centred at the distinguished point $\xi_\infty$ of the special fibre over $A$, so a point dominated by $R_1$ can be no other. It is used in identifying the reading map `readA` with the restriction of the $R_1$-residue at that point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_eq_xiInf_of_base_eq_closedPoint_of_forall_isUnit_germ_iff_residue_ne_zero.lean

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

theorem ModularCurve.XHDRModelAtP.eq_xiInf_of_base_eq_closedPoint_of_forall_isUnit_germ_iff_residue_ne_zero
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
      c = 𝔛.ξinf A hA ρ hρ ρ (IsLocalRing.residue ↥A) rfl := by sorry
