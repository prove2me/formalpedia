-- Prove2me | Theorems.Thm_GlobalTheory_CuspExist_exists_congr_diagonal
-- name    : GlobalTheory.CuspExist.exists_congr_diagonal
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:37:42.131804+00:00
-- url     : https://prove2.me/theorems/f3a89ae4-5f07-4175-9256-833b98687592
-- title:
--   Cusp Exist: exists congr diagonal
-- statement:
--   The Cusp Exist construction uses the exists congr diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/LinearIndependentSingleAdd.lean#L20-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/LinearIndependentSingleAdd.lean#L20-L91

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
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LandherrStOfHasseNormSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LinearIndependentSingleAdd
import Theorems.Thm_GlobalTheory_HermDiag_exists_congr_diagonal
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
open scoped Matrix ComplexConjugate
open GlobalTheory GlobalTheory.CuspExist
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.CuspExist.exists_congr_diagonal (H : GlobalTheory.Published.Landherr) (X : Data E r) (k : Fin r) :
    ∃ (d : E) (P : Matrix (Fin r) (Fin r) E), P.det ≠ 0 ∧
      Matrix.diagonal (fun a : Fin r => (if (a : ℕ) < X.p0 then (1 : E) else -1) *
        (if a = k then d else 1)) = Pᵀ * X.Gm * P.map cc := by sorry
