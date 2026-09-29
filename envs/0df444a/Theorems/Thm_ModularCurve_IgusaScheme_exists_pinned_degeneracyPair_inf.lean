-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_exists_pinned_degeneracyPair_inf
-- name    : ModularCurve.IgusaScheme.exists_pinned_degeneracyPair_inf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/49b36925-6150-5c31-aed0-979a0cd855b7
-- title:
--   Chart-pinned degeneracy pair between Igusa models of X₀(Mℓ) and X₀(M)
-- statement:
--   Fix natural numbers $M,q,\ell$ with $M\neq 0$ and $q,\ell$ prime, and a further natural number $M'\neq 0$ with $M'=M\ell$. Work over $R=$ [`GaloisRep.ratLocalizedAt q`](def/GaloisRep_Flat.html#L8), the subring of $\mathbb{Q}$ of rationals whose denominator is coprime to $q$. For a level $N$, `modularFunctionFieldFull N` is the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the series $j(q^{d})$ for all nonzero $d\mid N$; `chartAlgFin N q` and `chartAlgInf N q` are its $R$-subalgebras of elements integral over $R[j]$, respectively over $R[j^{-1}]$, and `IgusaScheme N q` is the two-chart scheme obtained by gluing their spectra, with structure morphism `igusaTo N q` to $\operatorname{Spec} R$. The theorem asserts the existence of two morphisms $\pi_1,\pi_2:$ `IgusaScheme M' q` $\to$ `IgusaScheme M q` over $\operatorname{Spec} R$, each finite and locally of finite presentation (these properties being bundled into the existential as anonymous witnesses) and surjective on underlying topological spaces, together with $R$-algebra maps $\iota_1,\iota_2:$ `chartAlgFin M q` $\to$ `chartAlgFin M' q` and $\iota_{I,1}:$ `chartAlgInf M q` $\to$ `chartAlgInf M' q`, such that on Laurent series $\iota_1$ and $\iota_{I,1}$ act as the identity while $\iota_2$ acts by $q\mapsto q^{\ell}$ (`qExpand ℚ ℓ`), and such that $\pi_1,\pi_2$ restricted to the $j$-finite chart of level $M'$ agree with $\operatorname{Spec}\iota_1$, $\operatorname{Spec}\iota_2$ followed by the $j$-finite chart of level $M$, and $\pi_1$ restricted to the pole chart agrees with $\operatorname{Spec}\iota_{I,1}$ followed by the pole chart. No pole-chart compatibility is claimed for $\pi_2$, and no flatness or degree statement is made.
--
--   These are the two degeneracy morphisms $X_0(M\ell)\to X_0(M)$, given classically on the upper half-plane by $\tau\mapsto\tau$ and $\tau\mapsto\ell\tau$, here realised on the integral two-chart (Igusa) models over $\mathbb{Z}_{(q)}$ and pinned on the charts by explicit maps of coordinate rings. The statement is used in the analysis of cusps, the Atkin–Lehner involution and the forgetful morphism on the smooth locus of the Deligne–Rapoport level structures.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_exists_pinned_degeneracyPair_inf.lean

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ModularCurve ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.exists_pinned_degeneracyPair_inf
    (M q ℓ : ℕ) [NeZero M] [Fact q.Prime] [Fact ℓ.Prime] (M' : ℕ) [NeZero M'] (hM' : M' = M * ℓ) :
    ∃ (π₁ π₂ : SchemeHomOver (IgusaScheme.igusaTo M' q) (IgusaScheme.igusaTo M q))
      (_ : IsFinite π₁.1) (_ : IsFinite π₂.1) (_ : LocallyOfFinitePresentation π₁.1) (_ : LocallyOfFinitePresentation π₂.1)
      (ι₁ ι₂ : ↥(IgusaScheme.chartAlgFin M q) →ₐ[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin M' q))
      (ιI₁ : ↥(IgusaScheme.chartAlgInf M q) →ₐ[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgInf M' q)),
      Function.Surjective π₁.1.base ∧ Function.Surjective π₂.1.base ∧
      (∀ b, (((ι₁ b : ↥(IgusaScheme.chartAlgFin M' q)) : ↥(modularFunctionFieldFull M')) : LaurentSeries ℚ) =
        ((b : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ)) ∧
      (∀ b, (((ι₂ b : ↥(IgusaScheme.chartAlgFin M' q)) : ↥(modularFunctionFieldFull M')) : LaurentSeries ℚ) =
        qExpand ℚ ℓ ((b : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ)) ∧
      IgusaScheme.ιFin M' q ≫ π₁.1 = Spec.map (CommRingCat.ofHom ι₁.toRingHom) ≫ IgusaScheme.ιFin M q ∧
      IgusaScheme.ιFin M' q ≫ π₂.1 = Spec.map (CommRingCat.ofHom ι₂.toRingHom) ≫ IgusaScheme.ιFin M q ∧

      (∀ b, (((ιI₁ b : ↥(IgusaScheme.chartAlgInf M' q)) : ↥(modularFunctionFieldFull M')) : LaurentSeries ℚ) =
        ((b : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ)) ∧
      IgusaScheme.ιInf M' q ≫ π₁.1 = Spec.map (CommRingCat.ofHom ιI₁.toRingHom) ≫ IgusaScheme.ιInf M q := by sorry
