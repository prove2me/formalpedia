-- Prove2me | Theorems.Thm_GlobalTheory_IsoExt_exists_gl_of_equiv
-- name    : GlobalTheory.IsoExt.exists_gl_of_equiv
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:21:37.586101+00:00
-- url     : https://prove2.me/theorems/16ebb215-e531-463e-8e53-60ebdd49753d
-- title:
--   Iso Ext: exists gl of equiv
-- statement:
--   The Iso Ext construction uses the exists gl of equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsUnitaryMatrixOfLatticeIsometry.lean#L19-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsUnitaryMatrixOfLatticeIsometry.lean#L19-L35

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
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLevelBlockOfEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUnitaryMatrixOfLatticeIsometry
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
open GlobalTheory GlobalTheory.IsoExt

theorem GlobalTheory.IsoExt.exists_gl_of_equiv {E : Type} [Field E] [NumberField E] {r : ℕ} {L L' : Type}
    [AddCommGroup L] [Module (𝓞 E) L] [AddCommGroup L'] [Module (𝓞 E) L']
    (φ : L →ₗ[𝓞 E] (Fin r → E)) (φ' : L' →ₗ[𝓞 E] (Fin r → E))
    (hφ : Function.Injective φ) (hspan : Submodule.span E (Set.range φ) = ⊤)
    (hφ' : Function.Injective φ') (hspan' : Submodule.span E (Set.range φ') = ⊤)
    (gam : L ≃ₗ[𝓞 E] L') : ∃ γ : GL (Fin r) E,
      ∀ v, (γ : Matrix (Fin r) (Fin r) E) *ᵥ φ v = φ' (gam v) := by sorry
