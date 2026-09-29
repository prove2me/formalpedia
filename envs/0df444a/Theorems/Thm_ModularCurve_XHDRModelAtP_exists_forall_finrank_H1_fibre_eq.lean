-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_forall_finrank_H1_fibre_eq
-- name    : ModularCurve.XHDRModelAtP.exists_forall_finrank_H1_fibre_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/5c273656-ca6d-5e4b-81a7-a7937e6c46b3
-- title:
--   Constant arithmetic genus of the geometric fibres at p
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number, let $H$ be a subgroup of $(\mathbb{Z}/M)^{\times}$, and assume $p \mid M$ while $p^{2} \nmid M$; let `hj` witness that the Laurent series `jqModC ℚ` lies in the intermediate field `qExpFunctionFieldC ℚ ⊤`, obtained by adjoining to $\mathbb{Q}$ the integral form ratios for $\mathrm{SL}(2,\mathbb{Z})$ inside $\mathbb{Q}((q))$. Let $\mathfrak{X}$ be a term of the structure `XHDRModelAtP p M H hpM hj`, i.e. a bundle of data and properties for the two-chart integral model `X p (ΓM M H) hj` over $\operatorname{Spec}(R\,p)$ with structure morphism $c =$ `toBase p (ΓM M H) hj`: properness, flatness, integrality and local finite presentation of $c$, integral closedness of the sections over each affine open, properness and relative-dimension-one smoothness of the auxiliary model at level `ΓN p M H hpM`, an identification of the geometric fibre over $\overline{\mathbb{Q}}$ with a smooth proper curve model of `xHFunctionFieldBar M H` compatible with the Galois action and pinned by $q$-expansions, smoothness and geometric integrality of the generic fibre, and further conditions, summarised here. The conclusion produces a single natural number $g$ such that for every algebraically closed field $k$, every morphism $x : \operatorname{Spec} k \to \operatorname{Spec}(R\,p)$, and every choice of two affine opens covering the fibre $\operatorname{pullback}(\operatorname{pullback.snd}\,c\,\mathrm{id})\,x$ and meeting in an affine open, the $k$-dimension of the two-chart Čech $H^{1}$ of the structure sheaf of that fibre, namely the quotient of the sections on the intersection by the image of the Čech difference, equals $g$.
--
--   This is the constancy of the arithmetic genus $\dim_k H^{1}(\mathcal{X}_x,\mathcal{O})$ over all geometric points of $\operatorname{Spec}(R\,p)$ for the Deligne–Rapoport model at level $\Gamma_H(M)$ with $p \| M$, computed through a two-chart Čech complex. It feeds the construction of the relative Picard scheme of the model and the genus computation relating the function field of $X_H$ over $\overline{\mathbb{Q}}$ to that of the residue fibre together with the supersingular node pairs.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_forall_finrank_H1_fibre_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_ModularCurve_XHDRModelAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_forall_finrank_H1_fibre_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj) :
    ∃ g : ℕ, ∀ (k : Type) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (R p)))
      (𝒲 : (pullback (pullback.snd (toBase p (ΓM M H) hj) (𝟙 (Spec (CommRingCat.of (R p))))) x).TwoAffineOpenCover),
      Module.finrank k (𝒲.sectionsOf (fibreAt (toBase p (ΓM M H) hj) (𝟙 _) x)
        (SheafOfModules.unit (pullback (pullback.snd (toBase p (ΓM M H) hj) (𝟙 (Spec (CommRingCat.of (R p))))) x).ringCatSheaf)).H1 = g := by sorry
