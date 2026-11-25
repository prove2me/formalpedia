-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_exists_siegelSet
-- name    : GroundTheory.Automorphic.Reduction.exists_siegelSet
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T06:37:49.64284+00:00
-- url     : https://prove2.me/theorems/59335f40-7586-4f2a-8d32-ab6355391ba1
-- title:
--   Reduction: exists siegel Set
-- statement:
--   The Reduction construction uses the exists siegel Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionSiegel.lean#L208-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionSiegel.lean#L208-L318

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionCore
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionSiegel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory.Global GroundTheory.Global.IdeleGroup
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K]
open scoped Pointwise

theorem GroundTheory.Automorphic.Reduction.exists_siegelSet (n : ℕ) :
    ∃ ω : Set (AdelicGLn.AdelicGL K n), IsCompact ω ∧
      ω ⊆ (adelicBorel (K := K) (n := n) : Set (AdelicGLn.AdelicGL K n)) ∧ ∃ t : ℝ, 0 < t ∧
      ∀ g : AdelicGLn.AdelicGL K n, ∃ γ : GL (Fin n) K,
        AdelicGLn.diagonal K n γ * g ∈ siegelSet n ω t := by sorry
