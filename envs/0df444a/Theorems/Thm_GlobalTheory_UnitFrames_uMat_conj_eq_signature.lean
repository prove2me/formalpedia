-- Prove2me | Theorems.Thm_GlobalTheory_UnitFrames_uMat_conj_eq_signature
-- name    : GlobalTheory.UnitFrames.uMat_conj_eq_signature
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:27:34.360668+00:00
-- url     : https://prove2.me/theorems/fdf640cd-ab1e-4e65-bb6d-d7980e6cab0d
-- title:
--   Unit Frames: u Mat conj eq signature
-- statement:
--   The Unit Frames construction uses the u Mat conj eq signature property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/UnitFrameEqOrthonormalMulTriangular.lean#L37-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/UnitFrameEqOrthonormalMulTriangular.lean#L37-L95

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_UnitFrameEqOrthonormalMulTriangular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.UnitFrames
open ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
variable {n : ℕ}

theorem GlobalTheory.UnitFrames.uMat_conj_eq_signature (p0 : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (hs : ∀ i : Fin (n + 1), 0 < psgn p0 i * (lminor A i).re)
    (h1 : ∀ i : Fin (n + 1), ‖lminor A i‖ = 1) :
    (uMat A)ᵀ * A * (uMat A).map (starRingEnd ℂ)
      = Matrix.diagonal fun a : Fin n => ((sgn p0 (a : ℕ) : ℝ) : ℂ) := by sorry
