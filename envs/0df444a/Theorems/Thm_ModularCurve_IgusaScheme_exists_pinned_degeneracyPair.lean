-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_exists_pinned_degeneracyPair
-- name    : ModularCurve.IgusaScheme.exists_pinned_degeneracyPair
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/e0e06a72-2a86-51b2-9bab-388fbce7babc
-- title:
--   Pinned degeneracy pair between Igusa schemes mathfrak X_{Mℓ}rightrightarrowsmathfrak X_M
-- statement:
--   Let $q$ and $\ell$ be primes, let $M$ and $M'$ be nonzero natural numbers with $M' = M\ell$, and write $R =$ [`GaloisRep.ratLocalizedAt q`](def/GaloisRep_Flat.html#L8), the subring of $\mathbb Q$ of rationals whose denominator is coprime to $q$. For a level $N$, `modularFunctionFieldFull N` is the subfield of $\mathbb{Q}((q))$ (Laurent series over $\mathbb Q$) generated over $\mathbb Q$ by the series $\mathrm{qExpand}\,\mathbb{Q}\,d\,j$ for $d \mid N$, `chartAlgFin N q` is the $R$-subalgebra of elements of that field integral over $R[j]$, and `IgusaScheme N q`, with structure morphism `igusaTo N q` to $\operatorname{Spec} R$, is the scheme obtained by gluing the two affine charts `chartAlgFin N q` and `chartAlgInf N q` along the middle chart. The assertion is that there exist two morphisms $\pi_1,\pi_2 \colon$ `IgusaScheme M' q` $\to$ `IgusaScheme M q` each commuting with the structure morphisms to $\operatorname{Spec} R$, proofs that both underlying morphisms are finite and locally of finite presentation, and $R$-algebra homomorphisms $\iota_1,\iota_2 \colon$ `chartAlgFin M q` $\to$ `chartAlgFin M' q`, such that the maps on underlying topological spaces of $\pi_1$ and $\pi_2$ are surjective; for every $b$ in `chartAlgFin M q` the Laurent series of $\iota_1 b$ equals that of $b$, while the Laurent series of $\iota_2 b$ is obtained from that of $b$ by $\mathrm{qExpand}\,\mathbb{Q}\,\ell$, i.e. by multiplying all exponents by $\ell$; and, for $i = 1,2$, the chart morphism `ιFin M' q` from $\operatorname{Spec}$ of `chartAlgFin M' q` followed by $\pi_i$ equals $\operatorname{Spec}$ of $\iota_i$ followed by `ιFin M q`. Only existence is asserted; no uniqueness or compatibility between $\pi_1$ and $\pi_2$ is claimed.
--
--   This is the pair of degeneracy morphisms $X_0(M\ell) \rightrightarrows X_0(M)$, realised on the two-chart integral models over $\mathbb{Z}_{(q)}$ and pinned by their effect on $q$-expansions ($f(\tau) \mapsto f(\tau)$ and $f(\tau)\mapsto f(\ell\tau)$), which is what identifies them as the two projections underlying the Hecke correspondence at $\ell$. It is used by [`ModularCurve.DRModelPackageLevel.exists_heckeDegeneracyPair`](thm.html#ModularCurve.DRModelPackageLevel.exists_heckeDegeneracyPair) in assembling the integral model package on which the Hecke action is built.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_exists_pinned_degeneracyPair.lean

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ModularCurve
open ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.exists_pinned_degeneracyPair
    (M q ℓ : ℕ) [NeZero M] [Fact q.Prime] [Fact ℓ.Prime] (M' : ℕ) [NeZero M'] (hM' : M' = M * ℓ) :
    ∃ (π₁ π₂ : SchemeHomOver (IgusaScheme.igusaTo M' q) (IgusaScheme.igusaTo M q))
      (_ : IsFinite π₁.1) (_ : IsFinite π₂.1) (_ : LocallyOfFinitePresentation π₁.1) (_ : LocallyOfFinitePresentation π₂.1)
      (ι₁ ι₂ : ↥(IgusaScheme.chartAlgFin M q) →ₐ[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin M' q)),
      Function.Surjective π₁.1.base ∧ Function.Surjective π₂.1.base ∧
      (∀ b, (((ι₁ b : ↥(IgusaScheme.chartAlgFin M' q)) : ↥(modularFunctionFieldFull M')) : LaurentSeries ℚ) =
        ((b : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ)) ∧
      (∀ b, (((ι₂ b : ↥(IgusaScheme.chartAlgFin M' q)) : ↥(modularFunctionFieldFull M')) : LaurentSeries ℚ) =
        qExpand ℚ ℓ ((b : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ)) ∧
      IgusaScheme.ιFin M' q ≫ π₁.1 = Spec.map (CommRingCat.ofHom ι₁.toRingHom) ≫ IgusaScheme.ιFin M q ∧
      IgusaScheme.ιFin M' q ≫ π₂.1 = Spec.map (CommRingCat.ofHom ι₂.toRingHom) ≫ IgusaScheme.ιFin M q := by sorry
