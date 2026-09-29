-- Prove2me | Theorems.Thm_ModularCurve_eq_cuspInftyBar_of_comap_toSubring_eq_cuspInftyFull
-- name    : ModularCurve.eq_cuspInftyBar_of_comap_toSubring_eq_cuspInftyFull
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/3d56d619-ae3c-5658-b988-2816b07ae57d
-- title:
--   Uniqueness of the place over the cusp ∞ after base change
-- statement:
--   Fix $N \geq 1$ and write $F_N =$ `modularFunctionFieldFull N` for the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the $q$-expansions `divisorExpansions N`, and $\bar{F}_N =$ `modularFunctionFieldBar N` for the subfield of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of $F_N$ under `coeffEmb`. Let $w$ be a place of $\bar{F}_N$ over $\overline{\mathbb{Q}}$ in the sense of the project's structure `Place`, i.e. a valuation subring $\mathcal{O}_w \subseteq \bar{F}_N$ containing the image of $\overline{\mathbb{Q}}$, different from $\bar{F}_N$ itself, and a principal ideal ring. Assume that the preimage of $\mathcal{O}_w$, as a subring, under the ring homomorphism $F_N \to \overline{\mathbb{Q}} \otimes_{\mathbb{Q}} F_N \to \bar{F}_N$ given by `Algebra.TensorProduct.includeRight` followed by `baseChangeEquiv`, is exactly the valuation subring of `cuspInftyFull N`, the $q$-adic place of $F_N$ (elements whose Laurent expansion has nonnegative order, with $j(q)$ as uniformiser witness of order $-1$). Then $w$ equals `cuspInftyBar N`, the corresponding $q$-adic place of $\bar{F}_N$.
--
--   This is the statement that the cusp $\infty$ of $X_0(N)$, being of degree one, has exactly one place above it in the constant field extension from $\mathbb{Q}$ to $\overline{\mathbb{Q}}$: a place of the geometric function field restricting to the rational cusp must be the geometric cusp. It is used to identify the place attached to the generic point of the cusp section on a curve model, in the computation of integral $q$-expansions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eq_cuspInftyBar_of_comap_toSubring_eq_cuspInftyFull.lean

import Mathlib
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_ModularCurve_HeckeProj
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_JacJ1Iface
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra ModularCurve AlgebraicCurve IsLocalRing CuspForm

theorem ModularCurve.eq_cuspInftyBar_of_comap_toSubring_eq_cuspInftyFull
    (N : ℕ) [NeZero N] (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hw : w.toValuationSubring.toSubring.comap
        ((baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull N)).toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ)
            (B := ↥(modularFunctionFieldFull N))).toRingHom) =
      (cuspInftyFull N).toValuationSubring.toSubring) :
    w = cuspInftyBar N := by sorry
