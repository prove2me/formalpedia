-- Prove2me | Theorems.Thm_GlobalTheory_FrameUnif_exists_den_herm_model
-- name    : GlobalTheory.FrameUnif.exists_den_herm_model
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:54:52.453576+00:00
-- url     : https://prove2.me/theorems/e7207ffa-2e00-481a-8251-56d216364652
-- title:
--   Frame Unif: exists den herm model
-- statement:
--   The Frame Unif construction uses the exists den herm model property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/LatticeModelOfSameSignatureHasseNorm.lean#L24-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/LatticeModelOfSameSignatureHasseNorm.lean#L24-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermitianFormsSameSignatureSameSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LandherrStOfHasseNormSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_PrincipalLevelGroupFiniteIndexUnitaryStabiliserStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_PrincipalGroupActsFreelyOnFlagsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TransvectionMemPrincipalCongruenceGroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LatticeModelOfSameSignatureHasseNorm
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_det

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
open GlobalTheory GlobalTheory.FrameUnif

theorem GlobalTheory.FrameUnif.exists_den_herm_model (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E)
    (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (hξ : cc ξ = -ξ)
    (h : Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧
      (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧
      ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm Gm (φ x) (φ y))) :
    ∃ den : 𝓞 E, den ≠ 0 ∧ ∀ x ∈ LinearMap.range φ, ∀ y ∈ LinearMap.range φ,
      IsIntegral ℤ ((den : E) * herm Gm x y) := by sorry
