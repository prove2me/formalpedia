-- Prove2me | Theorems.Thm_GroundTheory_Arith_Etale_existsUnique_pullbackSection
-- name    : GroundTheory.Arith.Etale.existsUnique_pullbackSection
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:27:37.07905+00:00
-- url     : https://prove2.me/theorems/dbff0b6b-72b4-477b-b075-3ca9a256cd44
-- title:
--   Etale: exists Unique pullback Section
-- statement:
--   The Etale construction uses the exists Unique pullback Section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/EtaleCompletion/PullbackAffine.lean#L214-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/EtaleCompletion/PullbackAffine.lean#L214-L229

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_ModulesPullback
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_PullbackAffine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Etale
open CategoryTheory Limits Opposite AlgebraicGeometry
universe u

theorem GroundTheory.Arith.Etale.existsUnique_pullbackSection {T U : Scheme.{u}} (g : T ⟶ U) [IsAffine T] [IsAffine U]
    (N : U.Modules) [N.IsQuasicoherent] (Q : Type u) [AddCommGroup Q] [Module Γ(T, ⊤) Q]
    (ψ : Γ(N, ⊤) →+ Q) (hψ : ∀ (a : Γ(U, ⊤)) (n : Γ(N, ⊤)), ψ (a • n) = g.appTop a • ψ n) :
    ∃! ψ' : Γ((Scheme.Modules.pullback g).obj N, ⊤) →ₗ[Γ(T, ⊤)] Q,
      ∀ n, ψ' (pullbackSection g N n) = ψ n := by sorry
