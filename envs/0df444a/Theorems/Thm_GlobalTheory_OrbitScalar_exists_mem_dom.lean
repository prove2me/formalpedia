-- Prove2me | Theorems.Thm_GlobalTheory_OrbitScalar_exists_mem_dom
-- name    : GlobalTheory.OrbitScalar.exists_mem_dom
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:45.704133+00:00
-- url     : https://prove2.me/theorems/d38e46cb-682a-4f62-b861-677c2b737e6c
-- title:
--   Orbit Scalar: exists mem dom
-- statement:
--   The Orbit Scalar construction uses the exists mem dom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsSmulOfPreservesFrameOrbits.lean#L17-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsSmulOfPreservesFrameOrbits.lean#L17-L29

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsSmulOfPreservesFrameOrbits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix
open GlobalTheory GlobalTheory.OrbitScalar
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
open NumberField
open scoped Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.OrbitScalar.exists_mem_dom (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) : X.dom.Nonempty := by sorry
