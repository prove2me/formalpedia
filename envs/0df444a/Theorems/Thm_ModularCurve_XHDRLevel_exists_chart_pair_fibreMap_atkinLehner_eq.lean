-- Prove2me | Theorems.Thm_ModularCurve_XHDRLevel_exists_chart_pair_fibreMap_atkinLehner_eq
-- name    : ModularCurve.XHDRLevel.exists_chart_pair_fibreMap_atkinLehner_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/145060db-0b18-5e1f-9c9d-4478aea36ca1
-- title:
--   Fibre charts compatible with an Atkin–Lehner chart square
-- statement:
--   Fix a prime $p$ and a nonzero $M$ with $p \mid M$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, and assume $j$-normalisation hypothesis `hj`, that the Laurent series `jqModC ℚ` (namely $q^{-1}$ times the integral power series `jNum`) lies in the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the ratios `intFormRatiosC ℚ ⊤`. Let $w$ be a self-isomorphism of the two-chart integral model `X p (ΓM M H) hj` over $R_p$, with `w_over` saying that $w$ followed by the structure morphism `toBase` to $\operatorname{Spec} R_p$ is again `toBase`, and let $\theta$ be an $R_p$-algebra automorphism of the $j$-finite chart algebra `chartAlgFin p (ΓM M H) hj` such that the chart inclusion `ιFin` followed by $w$ equals $\operatorname{Spec}\theta$ followed by `ιFin`. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$, whose residue field $\kappa$ is algebraically closed of characteristic $p$, and let $\rho : R_p \to A$ be a ring homomorphism compatible with the structure map $R_p \to \overline{\mathbb{Q}}$; give $\kappa$ the $R_p$-algebra structure obtained from $\rho$ followed by the residue map. Then there exist morphisms $c_0 : \operatorname{Spec}(\kappa \otimes_{R_p} \mathtt{chartAlgFin}\,p\,(\mathtt{ΓN}\,p\,M\,H\,hpM)\,hj) \to$ `fibre` at level `ΓN p M H hpM` and $c : \operatorname{Spec}(\kappa \otimes_{R_p} \mathtt{chartAlgFin}\,p\,(\mathtt{ΓM}\,M\,H)\,hj) \to$ `fibre` at level `ΓM M H`, where `fibre` denotes the pullback of `toBase` along $\operatorname{Spec}$ of the map $R_p \to \kappa$, such that for each of $c_0$ and $c$: composing with the first projection gives $\operatorname{Spec}$ of the right inclusion of the chart algebra into the tensor product followed by `ιFin`, composing with the second projection gives $\operatorname{Spec}$ of the left inclusion $\kappa \to \kappa \otimes_{R_p} -$; and moreover $c$ followed by the fibre map induced by $w$ (via `overOfIso w w_over` and `fibreMap`) equals $\operatorname{Spec}$ of $\mathrm{id}_{\kappa} \otimes \theta$ followed by $c$.
--
--   This packages the $j$-finite charts of the two $\kappa$-fibres of the integral models at levels `ΓN p M H hpM` and `ΓM M H`, together with the commuting square expressing that on the fibre the automorphism $w$ (in the applications an Atkin–Lehner involution) is induced by $\mathrm{id}_{\kappa} \otimes \theta$. It is stated so that the charts may be used as opaque data by [`ModularCurve.XHDRLevel.comp1_pi_place_and_pi_w_comp0_place_of_chart_atkinLehner`](thm.html#ModularCurve.XHDRLevel.comp1_pi_place_and_pi_w_comp0_place_of_chart_atkinLehner) and the further analysis of the fibre at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRLevel_exists_chart_pair_fibreMap_atkinLehner_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.XHDRLevel NeronModelInfra
open scoped MatrixGroups TensorProduct

theorem ModularCurve.XHDRLevel.exists_chart_pair_fibreMap_atkinLehner_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

    (w : X p (ΓM M H) hj ≅ X p (ΓM M H) hj) (w_over : w.hom ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj)
    (theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (hwchart : ιFin p (ΓM M H) hj ≫ w.hom = Spec.map (CommRingCat.ofHom theta.toRingEquiv.toRingHom) ≫ ιFin p (ΓM M H) hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) :
    letI := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
    ∃ (c₀ : Spec (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj))) ⟶
          fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (c : Spec (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) ⟶
          fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)),
      c₀ ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
          (R := R p) (A := IsLocalRing.ResidueField ↥A) (B := ↥(chartAlgFin p (ΓN p M H hpM) hj))).toRingHom) ≫ ιFin p (ΓN p M H hpM) hj ∧
      c₀ ≫ pullback.snd _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
          (R := R p) (A := IsLocalRing.ResidueField ↥A) (B := ↥(chartAlgFin p (ΓN p M H hpM) hj)))) ∧
      c ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
          (R := R p) (A := IsLocalRing.ResidueField ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) ≫ ιFin p (ΓM M H) hj ∧
      c ≫ pullback.snd _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
          (R := R p) (A := IsLocalRing.ResidueField ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj)))) ∧
      c ≫ fibreMap (overOfIso w w_over) ((IsLocalRing.residue ↥A).comp ρ) =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map
          (AlgHom.id (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥A)) theta.toAlgHom).toRingHom) ≫ c := by sorry
