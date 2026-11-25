-- Prove2me | Theorems.Thm_GlobalTheory_DefiniteFrames_isCompact_ortho
-- name    : GlobalTheory.DefiniteFrames.isCompact_ortho
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:41:26.26818+00:00
-- url     : https://prove2.me/theorems/7a522928-e647-46e7-a062-f33c6ac3f032
-- title:
--   Definite Frames: is Compact ortho
-- statement:
--   The Definite Frames construction uses the is Compact ortho property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsCompactOfDefinite.lean#L67-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsCompactOfDefinite.lean#L67-L96

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpolationModelInequalities
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_Frames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsCompactOfDefinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open GlobalTheory GlobalTheory.DefiniteFrames
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
open NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.DefiniteFrames.isCompact_ortho (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (hp : X.p0 = 0 ∨ r ≤ X.p0) :
    IsCompact {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r | X.IsOrtho x} := by sorry
