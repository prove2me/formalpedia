-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_mem_unitaryPoints
-- name    : GroundTheory.Automorphic.mem_unitaryPoints
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:53:53.312228+00:00
-- url     : https://prove2.me/theorems/d4ddd69a-8f97-5d97-b4ae-83cc30278e34
-- title:
--   Automorphic: mem unitary Points
-- statement:
--   The Automorphic construction uses the mem unitary Points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryGroupScheme.lean#L117-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryGroupScheme.lean#L117-L121

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryGroupScheme
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Module Matrix TensorProduct
variable (F E : Type*) [Field F] [CommRing E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)
variable (R S T : Type*) [CommRing R] [Algebra F R] [CommRing S] [Algebra F S]
  [CommRing T] [Algebra F T]
variable {F E H R S T}

theorem GroundTheory.Automorphic.mem_unitaryPoints {g : GL ι (R ⊗[F] E)} :
    g ∈ unitaryPoints F E H R ↔
      ((g : Matrix ι ι (R ⊗[F] E)).map (conjBase F E R))ᵀ *
        H.map (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E) * g =
      H.map (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E) := by sorry
