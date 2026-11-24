-- Prove2me | Theorems.Thm_GlobalTheory_mem_dualOE_xcFD_one_iff_of_adapted
-- name    : GlobalTheory.mem_dualOE_xcFD_one_iff_of_adapted
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:14:08.581045+00:00
-- url     : https://prove2.me/theorems/65878098-0c88-4155-a89d-8da812fa8952
-- title:
--   Global Theory: mem dual OE xc FD one iff of adapted
-- statement:
--   The Global Theory construction uses the mem dual OE xc FD one iff of adapted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/MemDualCuspCharacterLatticeIffAdaptedBasis.lean#L44-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/MemDualCuspCharacterLatticeIffAdaptedBasis.lean#L44-L85

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
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MemDualCuspCharacterLatticeIffAdaptedBasis
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
open GlobalTheory

theorem GlobalTheory.mem_dualOE_xcFD_one_iff_of_adapted : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu : FJ.CuspFD X ρ) (cc' : Fin ρ → FractionalIdeal (𝓞 E)⁰ E), (∀ a : Fin ρ → E, (∑ b, a b • cu.e b) ∈ X.Λ ↔ ∀ b, a b ∈ cc' b) → ∀ u : Fin ρ → E, u ∈ FJ.dualOE (FJ.XcFD 1 cu) ↔ ∀ a (y : E), (∀ a' ∈ cc' a, ∃ n : ℤ, Algebra.trace ℚ E (y * a') = n) → u a * y ∈ Set.range (algebraMap (𝓞 E) E) := by sorry
