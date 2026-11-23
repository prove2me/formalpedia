-- Prove2me | Theorems.Thm_GroundTheory_LocalField_toAdditive_cycNorm
-- name    : GroundTheory.LocalField.toAdditive_cycNorm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:00:25.479633+00:00
-- url     : https://prove2.me/theorems/df618c8b-ca9e-4290-96d2-a0288fe7bf6f
-- title:
--   Local Field: to Additive cyc Norm
-- statement:
--   The Local Field construction uses the to Additive cyc Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandCyclic.lean#L124-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandCyclic.lean#L124-L133

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_HerbrandCyclic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open GroundTheory.GroupCoh GroundTheory.Global
variable {G M : Type*} [Group G] [Fintype G] [CommGroup M] [MulDistribMulAction G M]
variable {σ : G}
variable {N : Type*} [CommGroup N] [MulDistribMulAction G N]

theorem GroundTheory.LocalField.toAdditive_cycNorm (i : M →* N) (hi : ∀ (g : G) (x : M), i (g • x) = g • i x)
    (x : Additive M) :
    MonoidHom.toAdditive i (cycNorm (Representation.ofMulDistribMulAction G M) x) =
      cycNorm (Representation.ofMulDistribMulAction G N) (MonoidHom.toAdditive i x) := by sorry
