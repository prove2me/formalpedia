-- Prove2me | Theorems.Thm_GlobalTheory_ExponentTrace_skew_iff
-- name    : GlobalTheory.ExponentTrace.skew_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:36:33.944548+00:00
-- url     : https://prove2.me/theorems/b55bc27a-656d-465e-9335-351a08dd5ad7
-- title:
--   Exponent Trace: skew iff
-- statement:
--   The Exponent Trace construction uses the skew iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CuspPairingIntIffHermitianExponentIntegral.lean#L156-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CuspPairingIntIffHermitianExponentIntegral.lean#L156-L209

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CmFieldHostElementAddConjEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ConjugateConjugate
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CuspPairingIntIffHermitianExponentIntegral
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
open GlobalTheory GlobalTheory.ExponentTrace
variable {E : Type} [Field E] [NumberField E]
variable [IsCMField E]

theorem GlobalTheory.ExponentTrace.skew_iff (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {r ρ : ℕ} (X : Data E r)
    (I : Fin ρ → Fin ρ → FractionalIdeal (𝓞 E)⁰ E) (hI : ∀ a b, ∀ s ∈ I a b, cc s ∈ I b a)
    (χ : Matrix (Fin ρ) (Fin ρ) E) (hχ : FJ.IsHermE χ) :
    (∀ β, FJ.IsSkew β → (∀ a b, β a b / X.ξ0 ∈ I a b) → ∃ n : ℤ, FJ.prE X χ β = n) ↔
      ∀ a b, ∀ s ∈ I a b, ∃ n : ℤ, Algebra.trace ℚ E (χ a b * s) = n := by sorry
