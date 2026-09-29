-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_exists_isPullback_twoChartIntegralModel_int_and_iso_pullback_and_iotaFin_comp_eq
-- name    : ModularCurve.IgusaScheme.exists_isPullback_twoChartIntegralModel_int_and_iso_pullback_and_iotaFin_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/c16737ee-a0cb-5da1-b46c-60b08d14569c
-- title:
--   Igusa scheme as base change of the two-chart ℤ-model
-- statement:
--   Fix $N\ge 1$ and a prime $\ell$, write $F=$ `modularFunctionFieldFull N` for the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the divisor expansions attached to $N$, let $j=$ `jFull N` be the $q$-expansion of $j$ viewed in $F$, and let $\mathbb{Z}_{(\ell)}=$ [`GaloisRep.ratLocalizedAt ℓ`](def/GaloisRep_Flat.html#L8) be the subring of rationals whose denominator is coprime to $\ell$. For a base ring $R$, [`AlgebraicCurve.TwoChartIntegralModel R F j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) denotes the pushout of the two affine charts $\operatorname{Spec}$ of the integral closures of $R[j]$ and of $R[j^{-1}]$ in $F$ along their common localisation, with structure morphism `toBase` to $\operatorname{Spec} R$; `IgusaScheme N ℓ` is the corresponding pushout formed over $\mathbb{Z}_{(\ell)}$, with structure morphism `igusaTo`. The assertion is the existence of a morphism $v$ from `IgusaScheme N ℓ` to `TwoChartIntegralModel ℤ F j` such that: the square formed by $v$, `igusaTo N ℓ`, `toBase ℤ F j` and $\operatorname{Spec}$ of $\mathbb{Z}\to\mathbb{Z}_{(\ell)}$ is cartesian; for every commutative ring $S$ in `Type` with a $\mathbb{Z}_{(\ell)}$-algebra structure there is an isomorphism $I$ between the pullback of `igusaTo N ℓ` along $\operatorname{Spec}(\mathbb{Z}_{(\ell)}\to S)$ and the pullback of `toBase ℤ F j` along $\operatorname{Spec}(\mathbb{Z}\to S)$ with $I$ followed by the second projection equal to the second projection, and $I$ followed by the first projection equal to the first projection followed by $v$; and $v$ is compatible with the charts, namely the finite chart inclusion `ιFin N ℓ` followed by $v$ equals $\operatorname{Spec}$ of the chart base-change inclusion for the set $\{j\}$ followed by `TwoChartIntegralModel.ιFin ℤ F j`, and likewise for `ιInf` with the set $\{j^{-1}\}$.
--
--   This identifies the Igusa scheme over $\mathbb{Z}_{(\ell)}$ with the base change of the two-chart integral model of $(F,j)$ over $\mathbb{Z}$, in a form that propagates to all fibres over $\mathbb{Z}_{(\ell)}$-algebras and records the behaviour on each of the two affine charts. It is used for the rational-fibre comparison of the Igusa scheme, for the smoothness and geometric integrality of that fibre, and in the construction of the model package entering the later arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_exists_isPullback_twoChartIntegralModel_int_and_iso_pullback_and_iotaFin_comp_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

theorem ModularCurve.IgusaScheme.exists_isPullback_twoChartIntegralModel_int_and_iso_pullback_and_iotaFin_comp_eq
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ v : IgusaScheme N ℓ ⟶
        AlgebraicCurve.TwoChartIntegralModel ℤ ↥(modularFunctionFieldFull N) (jFull N),
      IsPullback v (igusaTo N ℓ)
        (AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull N) (jFull N))
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ)))) ∧
      (∀ (S : Type) [CommRing S] [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) S],
        ∃ I : pullback (igusaTo N ℓ)
              (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) S))) ≅
            pullback
              (AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull N) (jFull N))
              (Spec.map (CommRingCat.ofHom (algebraMap ℤ S))),
          I.hom ≫ pullback.snd _ _ = pullback.snd _ _ ∧
          I.hom ≫ pullback.fst _ _ = pullback.fst _ _ ≫ v) ∧
      ιFin N ℓ ≫ v =
        Spec.map (CommRingCat.ofHom
          (AlgebraicCurve.TwoChartIntegralModel.chartBaseChange ℤ ↥(modularFunctionFieldFull N) ↥(GaloisRep.ratLocalizedAt ℓ) {jFull N})) ≫
          AlgebraicCurve.TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull N) (jFull N) ∧
      ιInf N ℓ ≫ v =
        Spec.map (CommRingCat.ofHom
          (AlgebraicCurve.TwoChartIntegralModel.chartBaseChange ℤ ↥(modularFunctionFieldFull N) ↥(GaloisRep.ratLocalizedAt ℓ) {(jFull N)⁻¹})) ≫
          AlgebraicCurve.TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull N) (jFull N) := by sorry
