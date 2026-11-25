-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_exists_reduced
-- name    : GroundTheory.Automorphic.Reduction.exists_reduced
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:11:12.772096+00:00
-- url     : https://prove2.me/theorems/678062e5-89c0-4e88-914e-72a3445c3bc3
-- title:
--   Reduction: exists reduced
-- statement:
--   The Reduction construction uses the exists reduced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionCore.lean#L409-L420
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionCore.lean#L409-L420

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionFinite
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionBlock
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionDirichlet
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionCore
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

theorem GroundTheory.Automorphic.Reduction.exists_reduced : ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ (n : ℕ) (g : AdelicGLn.AdelicGL K n),
    ∃ γ : GL (Fin n) K, ∃ b ∈ adelicBorel, ∃ k ∈ maxCompact,
      AdelicGLn.diagonal K n γ * g = b * k ∧ ∀ i j : Fin n, (j : ℕ) = i + 1 →
        t₀ * adeleAbs ((b : Matrix (Fin n) (Fin n) 𝔸[K]) j j) ≤
          adeleAbs ((b : Matrix (Fin n) (Fin n) 𝔸[K]) i i) := by sorry
