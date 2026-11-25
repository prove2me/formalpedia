-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_exists_reduced_of
-- name    : GroundTheory.Automorphic.Reduction.exists_reduced_of
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:10:54.401946+00:00
-- url     : https://prove2.me/theorems/33068b49-276b-431c-b965-986b777c1a98
-- title:
--   Reduction: exists reduced of
-- statement:
--   The Reduction construction uses the exists reduced of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionCore.lean#L225-L407
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionCore.lean#L225-L407

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

theorem GroundTheory.Automorphic.Reduction.exists_reduced_of {C : ℝ} (hC : 0 < C)
    (hD : ∀ (α δ : IdeleGroup K) (u : 𝔸[K]), ∃ x : Fin 2 → K, x ≠ 0 ∧
      adelicNorm (ratVec x ᵥ* !![(α : 𝔸[K]), u; 0, (δ : 𝔸[K])]) ≤
        C * √(ideleModule K (α * δ) : ℝ)) :
    ∀ (n : ℕ) (g : AdelicGLn.AdelicGL K n), ∃ γ : GL (Fin n) K, ∃ b ∈ adelicBorel, ∃ k ∈ maxCompact,
      AdelicGLn.diagonal K n γ * g = b * k ∧ ∀ i j : Fin n, (j : ℕ) = i + 1 →
        adeleAbs ((b : Matrix (Fin n) (Fin n) 𝔸[K]) j j) ≤
          C ^ 2 * adeleAbs ((b : Matrix (Fin n) (Fin n) 𝔸[K]) i i) := by sorry
