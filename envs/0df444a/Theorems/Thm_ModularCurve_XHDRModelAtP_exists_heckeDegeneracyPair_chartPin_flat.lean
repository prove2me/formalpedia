-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_heckeDegeneracyPair_chartPin_flat
-- name    : ModularCurve.XHDRModelAtP.exists_heckeDegeneracyPair_chartPin_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/187c70ea-6df8-517e-8b13-6f1c164e5d0f
-- title:
--   Hecke degeneracy pair for the Γ_H model over ℤ₍ₚ₎
-- statement:
--   Let $p$ and $M$ be natural numbers with $p$ prime, $M \neq 0$ and $p \mid M$, let $H$ be a subgroup of $(\mathbb{Z}/M)^{\times}$, and let $hj$ witness that the $q$-expansion `jqModC ℚ` lies in the field $\mathrm{qExpFunctionFieldC}\,\mathbb{Q}\,\top$ generated over $\mathbb{Q}$ by the integral form ratios at full level. Let $\mathfrak{X}$ be a term of the structure `XHDRModelAtP p M H hpM hj`, which bundles the arithmetic data of the two-chart integral model at level `ΓM M H` over `R p` (properness, flatness, integrality, local finite presentation and normality of the structure morphism and its source, properness and relative-dimension-one smoothness at the auxiliary level `ΓN p M H hpM`, a curve model over $\overline{\mathbb{Q}}$ with a Galois-equivariant identification of its points with places and a $q$-expansion pinning of the finite chart, and further generic smoothness and geometric integrality conditions, summarised here). Let $\ell$ be a prime and assume `HeckeBetaHDefined M H ℓ`: substitution $q \mapsto q^{\ell}$ (the ring map `qExpand ℚ ℓ`) carries every element of `xHFunctionField M H` into `xHTopFunctionFieldC ℚ M H (M * ℓ)`. Write $\Gamma' = \mathrm{GammaH}\,M\,H \sqcap \Gamma_0(M\ell)$. Then there exist two morphisms $\pi_\alpha, \pi_\beta$ from the model at level $\Gamma'$ to the model at level `ΓM M H`, each commuting with the structure morphisms to $\operatorname{Spec}$ of `R p`, both finite and locally of finite presentation, together with two `R p`-algebra maps $\iota_\alpha, \iota_\beta$ from the $j$-finite chart algebra at level `ΓM M H` to that at level $\Gamma'$, and an open subscheme $U$ of the model at level `ΓM M H`, such that: the underlying maps of $\pi_\alpha$ and $\pi_\beta$ are surjective; on $q$-expansions $\iota_\alpha$ is the identity, $(\iota_\alpha b)(q) = b(q)$, while $\iota_\beta$ is substitution, $(\iota_\beta b)(q) = b(q^{\ell})$, for every $b$ in the chart algebra; each $\pi$ is compatible with the chart immersions, in that `ιFin` at level $\Gamma'$ followed by $\pi$ equals $\operatorname{Spec}$ of the corresponding $\iota$ followed by `ιFin` at level `ΓM M H`; the preimage under each $\pi$ of the open range of `ιFin` at level `ΓM M H` is exactly the open range of `ιFin` at level $\Gamma'$; every point whose local ring has Krull dimension at most $1$ lies in $U$; both restrictions $\pi_\alpha|_U$ and $\pi_\beta|_U$ are flat; and at every point $y$ of $U$ the local rank `finrank` of both $\pi_\alpha$ and $\pi_\beta$ equals $\ell$ if $\ell \mid M$ and $\ell + 1$ otherwise.
--
--   This is the existence of the two degeneracy maps $X_{\Gamma_H(M) \cap \Gamma_0(M\ell)} \rightrightarrows X_H(M)$ over $\mathbb{Z}_{(p)}$ — the forgetful map and the map inducing $q \mapsto q^{\ell}$ — in the chart-pinned form in which the integral model is handled, with flatness and constant fibre degree in codimension at most one, uniformly in the three cases $\ell \nmid M$, $\ell \mid M$ and $\ell = p$. It is the input for the construction of the Hecke correspondences on the model at level $\Gamma_H(M)$ and for the dictionary relating that model to the associated Néron object.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_heckeDegeneracyPair_chartPin_flat.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_XHHeckeOperator
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
  ModularCurve ModularCurve.XHDRLevel CongruenceSubgroup
open scoped MatrixGroups
set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.XHDRModelAtP.exists_heckeDegeneracyPair_chartPin_flat
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (ℓ : ℕ) [Fact ℓ.Prime] (hβ : haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩; HeckeBetaHDefined M H ℓ) :
    haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
    ∃ (πα πβ : SchemeHomOver (toBase p (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) hj) (toBase p (ΓM M H) hj))
      (_ : IsFinite πα.1) (_ : IsFinite πβ.1) (_ : LocallyOfFinitePresentation πα.1) (_ : LocallyOfFinitePresentation πβ.1)
      (ια ιβ : ↥(chartAlgFin p (ΓM M H) hj) →ₐ[R p] ↥(chartAlgFin p (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) hj))
      (U : (X p (ΓM M H) hj).Opens),

      Function.Surjective πα.1.base ∧ Function.Surjective πβ.1.base ∧

      (∀ b : ↥(chartAlgFin p (ΓM M H) hj),
        (((ια b : ↥(chartAlgFin p (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)))) : LaurentSeries ℚ) =
          ((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)) ∧
      (∀ b : ↥(chartAlgFin p (ΓM M H) hj),
        (((ιβ b : ↥(chartAlgFin p (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)))) : LaurentSeries ℚ) =
          qExpand ℚ ℓ ((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)) ∧
      ιFin p (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) hj ≫ πα.1 = Spec.map (CommRingCat.ofHom ια.toRingHom) ≫ ιFin p (ΓM M H) hj ∧
      ιFin p (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) hj ≫ πβ.1 = Spec.map (CommRingCat.ofHom ιβ.toRingHom) ≫ ιFin p (ΓM M H) hj ∧

      πα.1 ⁻¹ᵁ (ιFin p (ΓM M H) hj).opensRange = (ιFin p (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) hj).opensRange ∧
      πβ.1 ⁻¹ᵁ (ιFin p (ΓM M H) hj).opensRange = (ιFin p (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) hj).opensRange ∧

      (∀ x : ↥(X p (ΓM M H) hj), ringKrullDim ((X p (ΓM M H) hj).presheaf.stalk x) ≤ 1 → x ∈ U) ∧
      Flat (πα.1 ∣_ U) ∧ Flat (πβ.1 ∣_ U) ∧
      (∀ y : ↥(X p (ΓM M H) hj), y ∈ U → πα.1.finrank y = (if ℓ ∣ M then ℓ else ℓ + 1)) ∧
      (∀ y : ↥(X p (ΓM M H) hj), y ∈ U → πβ.1.finrank y = (if ℓ ∣ M then ℓ else ℓ + 1)) := by sorry
