-- Prove2me | Theorems.Thm_ModularCurve_isIntegral_pullback_and_nonempty_of_chartMap_of_neZero
-- name    : ModularCurve.isIntegral_pullback_and_nonempty_of_chartMap_of_neZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/366fed4e-175a-5892-a100-289ca5c57c03
-- title:
--   Geometric generic fibre of a ℤ₍ₚ₎-model of X₀(N) is integral
-- statement:
--   Let $N \ge 1$ and let $p$ be a prime, and write $R =$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) for the subring of $\mathbf{Q}$ consisting of the rationals whose denominator is coprime to $p$. Let $X$ be a scheme and $c \colon X \to \operatorname{Spec} R$ a morphism with $X$ integral, $c$ proper and smooth of relative dimension $1$, and let $\mathcal{V}$ be a two-affine open cover of $X$, that is, a pair of affine opens $U_0, U_1$ with $U_0 \cap U_1$ affine and $U_0 \cup U_1 = X$. Put $A_0 = \Gamma(X, U_0)$, an $R$-algebra via $c$. Let $\iota \colon A_0 \to \overline{F}_N$ be a ring homomorphism into `modularFunctionFieldBar N`, the base change to $\overline{\mathbf{Q}}$, inside $\overline{\mathbf{Q}}((q))$, of the intermediate field $F_N =$ `modularFunctionFieldFull N` of $\mathbf{Q}((q))$ generated over $\mathbf{Q}$ by the divisor expansions of level $N$. Assume: $\iota$ is compatible with the structure maps, in that $\iota$ composed after $R \to A_0$ equals $R \hookrightarrow \overline{\mathbf{Q}} \to \overline{F}_N$; $\iota$ is injective; every $\iota(a)$, $a \in A_0$, is the coefficientwise image under `coeffEmb` of some element of $F_N$; and every $x \in F_N$ satisfies $\mathrm{coeffEmb}(x)\,\iota(b) = \iota(a)$ for some $a, b \in A_0$ with $\iota(b) \ne 0$. Then the pullback of $c$ along $\operatorname{Spec} \overline{\mathbf{Q}} \to \operatorname{Spec} R$ is an integral scheme, and the two opens of the pulled-back cover, namely the preimages of $U_0$ and of $U_1$ under the first projection, are both non-empty.
--
--   This is the statement that the geometric generic fibre of an integral proper smooth relative curve over $\mathbf{Z}_{(p)}$ whose chart $U_0$ is birationally identified with the modular function field of level $N$ is again integral, with both charts of the induced cover surviving the base change. It feeds the computations of regular differentials on such a model over $\overline{\mathbf{Q}}$, being used by [`ModularCurve.res_mem_regularDifferentialsBar_of_chartMap_of_neZero`](thm.html#ModularCurve.res_mem_regularDifferentialsBar_of_chartMap_of_neZero) and by [`ModularCurve.mem_span_range_res_of_mem_regularDifferentialsBar_of_chartMap_of_neZero`](thm.html#ModularCurve.mem_span_range_res_of_mem_regularDifferentialsBar_of_chartMap_of_neZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isIntegral_pullback_and_nonempty_of_chartMap_of_neZero.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import Definitions.Def_AlgebraicCurve_KaehlerToFunctionField

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve

theorem ModularCurve.isIntegral_pullback_and_nonempty_of_chartMap_of_neZero
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))) [IsIntegral X] [IsProper c]
    [SmoothOfRelativeDimension 1 c] (𝒱 : X.TwoAffineOpenCover)
    (ι : (𝒱.cover c).A0 →+* ↥(modularFunctionFieldBar N))
    (hιR : ι.comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (𝒱.cover c).A0) =
      (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))
    (hιinj : Function.Injective ι)
    (hιrat : ∀ a : (𝒱.cover c).A0, ∃ x ∈ modularFunctionFieldFull N,
      coeffEmb (AlgebraicClosure ℚ) x = (ι a : LaurentSeries (AlgebraicClosure ℚ)))
    (hιfrac : ∀ x ∈ modularFunctionFieldFull N, ∃ a b : (𝒱.cover c).A0, ι b ≠ 0 ∧
      coeffEmb (AlgebraicClosure ℚ) x * (ι b : LaurentSeries (AlgebraicClosure ℚ)) = ι a) :
    IsIntegral (pullback c (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))) ∧ Nonempty (𝒱.pullback c (AlgebraicClosure ℚ)).U0 ∧ Nonempty (𝒱.pullback c (AlgebraicClosure ℚ)).U1 := by sorry
