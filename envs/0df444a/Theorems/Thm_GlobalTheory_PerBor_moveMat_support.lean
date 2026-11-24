-- Prove2me | Theorems.Thm_GlobalTheory_PerBor_moveMat_support
-- name    : GlobalTheory.PerBor.moveMat_support
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:06:09.774252+00:00
-- url     : https://prove2.me/theorems/2557f0c2-1cb0-4eaa-adee-13b82076f9e6
-- title:
--   Per Bor: move Mat support
-- statement:
--   The Per Bor construction uses the move Mat support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/TriangularFrameMovesPeriodBlockTriangular.lean#L88-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/TriangularFrameMovesPeriodBlockTriangular.lean#L88-L101

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CmTypeLetterFrameColumnDictionaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RelabelEmbeddingsGoodBijectiveConjCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetOfTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TriangularFrameMovesPeriodBlockTriangular
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
open GlobalTheory GlobalTheory.PerBor
variable {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r g : ℕ} (q : ℕ) (idx : Fin g ≃ Ψ × Fin r)
    {b : Frame Ψ r}

theorem GlobalTheory.PerBor.moveMat_support (hb : b ∈ Bor Ψ r) (k l : Fin g) (h : moveMat q idx b k l ≠ 0) :
    (idx l).1 = (idx k).1 ∧ (if ((idx k).2 : ℕ) < q then ((idx l).2 : ℕ) ≤ (idx k).2
      else ((idx k).2 : ℕ) ≤ (idx l).2) := by sorry
