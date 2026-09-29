-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_twoGluedSmoothCurves_isReduced_pullback_of_ker_ne_bot
-- name    : ModularCurve.XHDRModelAtP.exists_twoGluedSmoothCurves_isReduced_pullback_of_ker_ne_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/f6995961-01ef-5005-a8bb-9c265fb75661
-- title:
--   Geometric closed fibres as two transversally glued smooth curves
-- statement:
--   Fix a prime $p$ and a non-zero natural number $M$ with $p \mid M$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, and the hypothesis `hj` that the Laurent series `jqModC ℚ` lies in `qExpFunctionFieldC ℚ ⊤`, the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the ratios of integral forms for the full modular group. Let $\mathfrak{X}$ be a term of the structure `XHDRModelAtP p M H hpM hj`, the bundled data and properties of the two-chart integral model `toBase p (ΓM M H) hj` of the modular curve of level $\Gamma_H(M)$ over the base ring `R p`. Let $k$ be an algebraically closed field and $f :$ `R p` $\to k$ a ring homomorphism whose kernel is non-zero, and write $Z$ for the pullback of `toBase p (ΓM M H) hj` along $\mathrm{Spec}(f)$, with second projection $Z \to \mathrm{Spec}\,k$. Then there exist schemes $C_1, C_2$ with morphisms $c_1 : C_1 \to \mathrm{Spec}\,k$, $c_2 : C_2 \to \mathrm{Spec}\,k$, each proper, smooth of relative dimension $1$ and geometrically integral; morphisms $i_1 : C_1 \to Z$ and $i_2 : C_2 \to Z$ over $\mathrm{Spec}\,k$ (that is, whose composites with the projection $Z \to \mathrm{Spec}\,k$ are $c_1$, resp. $c_2$), both closed immersions; a natural number $n$; and for each of $C_1$, $C_2$ a cover by two affine opens $U_0, U_1$ with $U_0 \sqcup U_1 = \top$ and $U_0 \sqcap U_1$ affine, such that $Z$ is reduced, every point of $Z$ lies in the image of the underlying map of $i_1$ or of $i_2$, and the scheme-theoretic pullback $C_1 \times_Z C_2$ is reduced with exactly $n$ points, $n > 0$.
--
--   This is the assertion that every geometric closed fibre of the integral model of $X_H(M)$ at a prime $p$ exactly dividing the level is the union of two smooth proper geometrically integral curves, meeting in a finite non-empty reduced crossing locus; in the classical literature this is the Deligne–Rapoport description of the special fibre at such a level. It supplies exactly the special-fibre hypothesis used by the two statements producing Hecke homomorphisms along `toBase p (ΓM M H) hj`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_twoGluedSmoothCurves_isReduced_pullback_of_ker_ne_bot.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
  ModularCurve ModularCurve.XHDRLevel CongruenceSubgroup
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_twoGluedSmoothCurves_isReduced_pullback_of_ker_ne_bot
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (k : Type) [Field k] [IsAlgClosed k] (f : R p →+* k) (hf : RingHom.ker f ≠ ⊥) :
    ∃ (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
      (_ : IsProper c₁) (_ : SmoothOfRelativeDimension 1 c₁) (_ : GeometricallyIntegral c₁)
      (_ : IsProper c₂) (_ : SmoothOfRelativeDimension 1 c₂) (_ : GeometricallyIntegral c₂)
      (i₁ : SchemeHomOver c₁ (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom f))))
      (i₂ : SchemeHomOver c₂ (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom f))))
      (_ : IsClosedImmersion i₁.1) (_ : IsClosedImmersion i₂.1) (n : ℕ)
      (_ : C₁.TwoAffineOpenCover) (_ : C₂.TwoAffineOpenCover),
      IsReduced (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom f))) ∧
      (∀ z : ↥(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom f))), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base) ∧
      IsReduced (pullback i₁.1 i₂.1) ∧ Nat.card ↥(pullback i₁.1 i₂.1) = n ∧ 0 < n := by sorry
