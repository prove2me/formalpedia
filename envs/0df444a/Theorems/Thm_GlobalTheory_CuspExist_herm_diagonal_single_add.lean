-- Prove2me | Theorems.Thm_GlobalTheory_CuspExist_herm_diagonal_single_add
-- name    : GlobalTheory.CuspExist.herm_diagonal_single_add
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:37:28.157471+00:00
-- url     : https://prove2.me/theorems/4fc56dd0-f3a8-4282-a92b-b94168c2891e
-- title:
--   Cusp Exist: herm diagonal single add
-- statement:
--   The Cusp Exist construction uses the herm diagonal single add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/LinearIndependentSingleAdd.lean#L104-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/LinearIndependentSingleAdd.lean#L104-L116

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

theorem GlobalTheory.CuspExist.herm_diagonal_single_add {ρ : ℕ} {i j : Fin ρ → Fin r} (hi : Function.Injective i)
    (hj : Function.Injective j) (hij : ∀ a b, i a ≠ j b) (g : Fin r → E)
    (hg : ∀ a, g (i a) + g (j a) = 0) (a b : Fin ρ) :
    herm (Matrix.diagonal g) (Pi.single (i a) 1 + Pi.single (j a) 1)
      (Pi.single (i b) 1 + Pi.single (j b) 1) = 0 := by sorry
