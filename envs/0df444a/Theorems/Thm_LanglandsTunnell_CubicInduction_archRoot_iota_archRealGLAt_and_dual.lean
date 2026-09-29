-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_archRoot_iota_archRealGLAt_and_dual
-- name    : LanglandsTunnell.CubicInduction.archRoot_iota_archRealGLAt_and_dual
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/320148c1-0f14-52de-93e3-82f90c346e33
-- title:
--   Archimedean root sizes of a GL₂ block image and its dual
-- statement:
--   Let $h \in \mathrm{GL}_2(\mathbb{R})$ and let $w$ be an infinite place of $\mathbb{Q}$. Write $g \in \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ for the image of $h$ under the composite `iota ∘ archRealGLAt`: first $h$ is transported along the ring isomorphism between $\mathbb{R}$ and the completion of $\mathbb{Q}$ at the default infinite place (which is real, $\mathbb{Q}$ being totally real), then included as the archimedean component of an adelic $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ element, and finally embedded in $\mathrm{GL}_3$ by the block map `embedMat2`. Put $s = h_{10}^2 + h_{11}^2$, the squared Euclidean length of the second row of $h$, and $d = |\det h|$. The assertion is the conjunction of four equalities: `archRoot₁` of $\mathbb{Q}$ at $w$ evaluated at $g$ equals $d/s$, and `archRoot₂` at $g$ equals $\sqrt{s}$; while for the dual point $w_3 \cdot {}^{t}g^{-1}$, where $w_3 =$ `longWeyl3` is the antidiagonal permutation matrix in $\mathrm{GL}_3$ and `transposeInv3` sends $g$ to the transpose of $g^{-1}$, the two values are interchanged: `archRoot₁` gives $\sqrt{s}$ and `archRoot₂` gives $d/s$.
--
--   This is the explicit computation of the two archimedean simple-root size functions on the mirabolic-type $\mathrm{GL}_3$ image of a point of $\mathrm{GL}_2(\mathbb{R})$, and on its dual point, in terms of $|\det h|$ and the second row of $h$. It is used in the Rankin–Selberg part of the Langlands–Tunnell argument, in [`LanglandsTunnell.RankinSelberg.exists_forall_integrable_archWhittaker_torusPair_rpow_det`](thm.html#LanglandsTunnell.RankinSelberg.exists_forall_integrable_archWhittaker_torusPair_rpow_det), where the resulting gauge bounds give integrability of archimedean Whittaker majorants against powers of the determinant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_archRoot_iota_archRealGLAt_and_dual.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_DeltaLift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem LanglandsTunnell.CubicInduction.archRoot_iota_archRealGLAt_and_dual (h : GL (Fin 2) ℝ) (w : InfinitePlace ℚ) :
    archRoot₁ ℚ w (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) h)) =
        |(Matrix.GeneralLinearGroup.det h : ℝ)| /
          (((h : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((h : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) ∧
      archRoot₂ ℚ w (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) h)) =
        Real.sqrt (((h : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((h : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) ∧
      archRoot₁ ℚ w (longWeyl3 * transposeInv3
          (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) h))) =
        Real.sqrt (((h : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((h : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) ∧
      archRoot₂ ℚ w (longWeyl3 * transposeInv3
          (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) h))) =
        |(Matrix.GeneralLinearGroup.det h : ℝ)| /
          (((h : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((h : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) := by sorry
