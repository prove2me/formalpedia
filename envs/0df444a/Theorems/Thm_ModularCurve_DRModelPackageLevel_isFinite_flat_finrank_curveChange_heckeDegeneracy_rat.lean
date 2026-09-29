-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_isFinite_flat_finrank_curveChange_heckeDegeneracy_rat
-- name    : ModularCurve.DRModelPackageLevel.isFinite_flat_finrank_curveChange_heckeDegeneracy_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/8961941c-c35f-5158-a966-02d6615082bf
-- title:
--   Generic fibre degeneracy maps are finite flat of constant rank
-- statement:
--   Fix natural numbers $N_0$ and $q$ with $N_0 \neq 0$ and $q$ prime, a proof $hqN$ that $q \nmid N_0$, and a prime $\ell$ together with a proof $hqN\ell$ that $q \nmid N_0\ell$. Let $\pi_1,\pi_2$ be morphisms of schemes over $\operatorname{Spec}(\mathtt{DRLevel.R}\,q)$ from the level-$N_0\ell$ Igusa-type model to the level-$N_0$ one, i.e. pairs consisting of a morphism $\mathtt{X}(N_0\ell)\;q \to \mathtt{X}(N_0)\;q$ together with the identity $\varphi \text{ followed by } \mathtt{toBase}\,N_0\,q = \mathtt{toBase}\,(N_0\ell)\,q$, where $\mathtt{toBase}\,M\,q = \mathtt{IgusaScheme.igusaTo}\,(Mq)\,q$. Let $\iota_1,\iota_2$ be $\mathtt{DRLevel.R}\,q$-algebra maps $\mathtt{chartAlgFin}(N_0q)\,q \to \mathtt{chartAlgFin}(N_0\ell q)\,q$ such that, read inside $\mathbb{Q}$-Laurent series through the modular function fields, $\iota_1$ is the inclusion of $q$-expansions and $\iota_2$ is the operator $\mathtt{qExpand}\ \mathbb{Q}\ \ell$ scaling exponents by $\ell$; assume each $\pi_i$ is pinned on the finite chart, namely $\mathtt{ιFin}(N_0\ell q)\,q$ followed by $\pi_i$ equals $\operatorname{Spec}(\iota_i)$ followed by $\mathtt{ιFin}(N_0q)\,q$. The conclusion asserts: the base changes along $\operatorname{Spec}\mathbb{Q} \to \operatorname{Spec}(\mathtt{DRLevel.R}\,q)$, formed as $\pi_i \times \mathrm{id}$ on the respective pullbacks, are finite, locally of finite presentation and flat, and their $\mathtt{finrank}$ at every point of the target equals $\ell$ if $\ell \mid N_0$ and $\ell+1$ otherwise.
--
--   This is the generic-fibre statement that the two degeneracy maps $X_0(N_0\ell q)_{\mathbb{Q}} \rightrightarrows X_0(N_0 q)_{\mathbb{Q}}$, given on $q$-expansions by $\tau \mapsto \tau$ and $\tau \mapsto \ell\tau$, are finite locally free of degree $[\Gamma_0(N_0q) : \Gamma_0(N_0\ell q)]$. It supplies the pair of finite flat morphisms of constant rank used by [`ModularCurve.DRModelPackageLevel.exists_hom_mul_and_pts_heckeOperatorBar_eq_comp_of_ne`](thm.html#ModularCurve.DRModelPackageLevel.exists_hom_mul_and_pts_heckeOperatorBar_eq_comp_of_ne) to realise the Hecke operator on the relative Jacobian as a pull-back followed by a push-forward.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_isFinite_flat_finrank_curveChange_heckeDegeneracy_rat.lean

import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel
namespace ModularCurve.DRModelPackageLevel

theorem isFinite_flat_finrank_curveChange_heckeDegeneracy_rat (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)
    (ℓ : ℕ) [Fact ℓ.Prime] (hqNℓ : ¬ q ∣ N₀ * ℓ)
    (π₁ π₂ : SchemeHomOver (DRLevel.toBase (N₀ * ℓ) q) (DRLevel.toBase N₀ q))
    (ι₁ ι₂ : ↥(IgusaScheme.chartAlgFin (N₀ * q) q) →ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * ℓ * q) q))
    (hι₁ : ∀ b, (((ι₁ b : ↥(IgusaScheme.chartAlgFin (N₀ * ℓ * q) q)) : ↥(modularFunctionFieldFull (N₀ * ℓ * q))) : LaurentSeries ℚ) =
        ((b : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ))
    (hι₂ : ∀ b, (((ι₂ b : ↥(IgusaScheme.chartAlgFin (N₀ * ℓ * q) q)) : ↥(modularFunctionFieldFull (N₀ * ℓ * q))) : LaurentSeries ℚ) =
        qExpand ℚ ℓ ((b : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ))
    (hπ₁ : IgusaScheme.ιFin (N₀ * ℓ * q) q ≫ π₁.1 = Spec.map (CommRingCat.ofHom ι₁.toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q)
    (hπ₂ : IgusaScheme.ιFin (N₀ * ℓ * q) q ≫ π₂.1 = Spec.map (CommRingCat.ofHom ι₂.toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q) :
    ∃ (_ : IsFinite (RelPicard.curveChange π₁.1 π₁.2 (SmoothProperCurve.specMap (DRLevel.R q) ℚ)))
      (_ : IsFinite (RelPicard.curveChange π₂.1 π₂.2 (SmoothProperCurve.specMap (DRLevel.R q) ℚ)))
      (_ : LocallyOfFinitePresentation (RelPicard.curveChange π₁.1 π₁.2 (SmoothProperCurve.specMap (DRLevel.R q) ℚ)))
      (_ : LocallyOfFinitePresentation (RelPicard.curveChange π₂.1 π₂.2 (SmoothProperCurve.specMap (DRLevel.R q) ℚ))),
      Flat (RelPicard.curveChange π₁.1 π₁.2 (SmoothProperCurve.specMap (DRLevel.R q) ℚ)) ∧
      Flat (RelPicard.curveChange π₂.1 π₂.2 (SmoothProperCurve.specMap (DRLevel.R q) ℚ)) ∧
      (∀ y, (RelPicard.curveChange π₁.1 π₁.2 (SmoothProperCurve.specMap (DRLevel.R q) ℚ)).finrank y = (if ℓ ∣ N₀ then ℓ else ℓ + 1)) ∧
      (∀ y, (RelPicard.curveChange π₂.1 π₂.2 (SmoothProperCurve.specMap (DRLevel.R q) ℚ)).finrank y = (if ℓ ∣ N₀ then ℓ else ℓ + 1)) := by sorry
