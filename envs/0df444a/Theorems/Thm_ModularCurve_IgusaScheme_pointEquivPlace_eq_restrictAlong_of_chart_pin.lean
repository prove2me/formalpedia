-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_pointEquivPlace_eq_restrictAlong_of_chart_pin
-- name    : ModularCurve.IgusaScheme.pointEquivPlace_eq_restrictAlong_of_chart_pin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/212ddb6e-f2e5-5a4c-b2c6-766cd39dfb32
-- title:
--   Places restrict along chart-pinned morphisms of Igusa schemes
-- statement:
--   Fix nonzero levels $M,M'$ and a prime $p$, and write $R=$ `R p` for $\mathbb{Z}$ localised at $p$, with `genPt p` the $\overline{\mathbb{Q}}$-point $\operatorname{Spec}\overline{\mathbb{Q}}\to\operatorname{Spec}R$. For $N\in\{M,M'\}$ let `modularFunctionFieldBar N` be the subfield of $\overline{\mathbb{Q}}$-Laurent series generated over $\overline{\mathbb{Q}}$ by the coefficientwise images under `coeffEmb` of `modularFunctionFieldFull N`, and let `chartAlgFin N p` be the subalgebra of `modularFunctionFieldFull N` of elements integral over $R[j]$, with `ιFin N p` the corresponding chart of `IgusaScheme N p` and `igusaTo N p` its structure morphism to $\operatorname{Spec}R$. Assume given: `CurveModel`s $C_2$, $C_1$ over $\overline{\mathbb{Q}}$ of `modularFunctionFieldBar M'`, `modularFunctionFieldBar M` (integral proper smooth curves of relative dimension $1$ with a ring isomorphism onto the function field over the base and a bijection from closed points to places matching stalk images with valuation subrings); isomorphisms $e_2,e_1$ from $C_2.C$, $C_1.C$ to the fibre products of `igusaTo` with `genPt p`, compatible with the base morphisms; nonemptiness of the preimage under $e_i$ followed by the first projection of the image of the finite chart; and pinning hypotheses `pin₂`, `pin₁` saying that for every $b$ in `chartAlgFin M' p` (resp. $a$ in `chartAlgFin M p`) the generic germ over that open of the pullback of $b$ (resp. $a$) along $e_i$ followed by the first projection corresponds, under the function-field identification, to `coeffEmb` of the $q$-expansion of $b$ (resp. $a$). Assume further an $R$-algebra map $\theta$ from `chartAlgFin M p` to `chartAlgFin M' p`, a $\overline{\mathbb{Q}}$-algebra map $\Phi$ from `modularFunctionFieldBar M` to `modularFunctionFieldBar M'` with $\Phi(\mathrm{coeffEmb}\,a)=\mathrm{coeffEmb}(\theta a)$ for all $a$, a morphism $\pi_X : \mathrm{IgusaScheme}\,M'\,p \to \mathrm{IgusaScheme}\,M\,p$ over $\operatorname{Spec}R$ whose restriction to the finite charts is $\operatorname{Spec}\theta$ (i.e. `ιFin M' p` followed by $\pi_X$ equals $\operatorname{Spec}\theta$ followed by `ιFin M p`), integrality of $\Phi$ as a ring homomorphism, and finiteness of `modularFunctionFieldBar M'` as a module over `modularFunctionFieldBar M` via $\Phi$. Then for $\overline{\mathbb{Q}}$-points $y$ of $C_2$ and $x$ of $C_1$ (sections of the structure morphisms) such that $x$ followed by $e_1$ and the first projection equals $y$ followed by $e_2$, the first projection and $\pi_X$, the place of `modularFunctionFieldBar M` attached to $x$ by $C_1$'s point-place bijection equals the restriction along $\Phi$ (the preimage of the valuation subring) of the place attached to $y$ by $C_2$'s bijection.
--
--   This is the statement that a morphism of Igusa schemes which is $\operatorname{Spec}\theta$ on the $j$-finite charts induces, on the geometric generic fibres viewed as smooth proper $\overline{\mathbb{Q}}$-curves pinned by $q$-expansions, the map of places given by restriction along the associated $\overline{\mathbb{Q}}$-algebra map $\Phi$ of modular function fields. It is the transfer between the scheme-theoretic and valuation-theoretic descriptions used when degeneracy maps and Hecke correspondences are constructed on the Deligne–Rapoport level packages, and is cited in the construction of the Hecke operators there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_pointEquivPlace_eq_restrictAlong_of_chart_pin.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_LevelModel
import Definitions.Def_ModularCurve_ToricDescentData
import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve ModularCurve.DRLevel
  ModularCurve.JZeroNeronObjectAtP AlgebraicCurve
open Topology
open scoped TensorProduct

theorem ModularCurve.IgusaScheme.pointEquivPlace_eq_restrictAlong_of_chart_pin
    (M M' p : ℕ) [NeZero M] [NeZero M'] [Fact p.Prime]

    (C₂ : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar M'))
    (e₂ : C₂.C ⟶ pullback (IgusaScheme.igusaTo M' p) (genPt p)) [IsIso e₂] (he₂ : e₂ ≫ pullback.snd _ _ = C₂.toBase)
    (hne₂ : Nonempty (Scheme.Opens.toScheme ((e₂ ≫ pullback.fst (IgusaScheme.igusaTo M' p) (genPt p)) ⁻¹ᵁ ((IgusaScheme.ιFin M' p) ''ᵁ ⊤))))
    (pin₂ : ∀ b : ↥(IgusaScheme.chartAlgFin M' p),
      ((C₂.ffEquiv.symm
          (C₂.C.germToFunctionField
            ((e₂ ≫ pullback.fst (IgusaScheme.igusaTo M' p) (genPt p)) ⁻¹ᵁ ((IgusaScheme.ιFin M' p) ''ᵁ ⊤))
            (((e₂ ≫ pullback.fst (IgusaScheme.igusaTo M' p) (genPt p)).app ((IgusaScheme.ιFin M' p) ''ᵁ ⊤)).hom
              (((IgusaScheme.ιFin M' p).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin M' p))).inv b))))
          : ↥(modularFunctionFieldBar M')) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull M')) : LaurentSeries ℚ))

    (C₁ : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar M))
    (e₁ : C₁.C ⟶ pullback (IgusaScheme.igusaTo M p) (genPt p)) [IsIso e₁] (he₁ : e₁ ≫ pullback.snd _ _ = C₁.toBase)
    (hne₁ : Nonempty (Scheme.Opens.toScheme ((e₁ ≫ pullback.fst (IgusaScheme.igusaTo M p) (genPt p)) ⁻¹ᵁ ((IgusaScheme.ιFin M p) ''ᵁ ⊤))))
    (pin₁ : ∀ a : ↥(IgusaScheme.chartAlgFin M p),
      ((C₁.ffEquiv.symm
          (C₁.C.germToFunctionField
            ((e₁ ≫ pullback.fst (IgusaScheme.igusaTo M p) (genPt p)) ⁻¹ᵁ ((IgusaScheme.ιFin M p) ''ᵁ ⊤))
            (((e₁ ≫ pullback.fst (IgusaScheme.igusaTo M p) (genPt p)).app ((IgusaScheme.ιFin M p) ''ᵁ ⊤)).hom
              (((IgusaScheme.ιFin M p).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin M p))).inv a))))
          : ↥(modularFunctionFieldBar M)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ))
    (θ : ↥(IgusaScheme.chartAlgFin M p) →ₐ[R p] ↥(IgusaScheme.chartAlgFin M' p))
    (Φ : ↥(modularFunctionFieldBar M) →ₐ[AlgebraicClosure ℚ] ↥(modularFunctionFieldBar M'))
    (hΦθ : ∀ a : ↥(IgusaScheme.chartAlgFin M p),
      ((Φ ⟨coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (a : ↥(modularFunctionFieldFull M)).2⟩ :
          ↥(modularFunctionFieldBar M')) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) (((θ a : ↥(IgusaScheme.chartAlgFin M' p)) :
          ↥(modularFunctionFieldFull M')) : LaurentSeries ℚ))
    (πX : IgusaScheme M' p ⟶ IgusaScheme M p) (hπX : πX ≫ IgusaScheme.igusaTo M p = IgusaScheme.igusaTo M' p)
    (hchart : IgusaScheme.ιFin M' p ≫ πX = Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ IgusaScheme.ιFin M p)

    (hint : Φ.toRingHom.IsIntegral) (hfin : FiniteAlong (AlgebraicClosure ℚ) Φ)

    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ C₂.C // q ≫ C₂.toBase = 𝟙 _})
    (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ C₁.C // q ≫ C₁.toBase = 𝟙 _})
    (hyx : x.1 ≫ e₁ ≫ pullback.fst (IgusaScheme.igusaTo M p) (genPt p) =
      y.1 ≫ e₂ ≫ pullback.fst (IgusaScheme.igusaTo M' p) (genPt p) ≫ πX) :
    C₁.pointEquivPlace x = (C₂.pointEquivPlace y).restrictAlong Φ hint := by sorry
