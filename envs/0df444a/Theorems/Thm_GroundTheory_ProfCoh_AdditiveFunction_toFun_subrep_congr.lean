-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_toFun_subrep_congr
-- name    : GroundTheory.ProfCoh.AdditiveFunction.toFun_subrep_congr
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:48:05.411197+00:00
-- url     : https://prove2.me/theorems/85def13a-8b3c-4dc8-8884-a5c8d38444b8
-- title:
--   Additive Function: to Fun subrep congr
-- statement:
--   The Additive Function construction uses the to Fun subrep congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/AdditiveSnake.lean#L74-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/AdditiveSnake.lean#L74-L78

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveSnake
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
universe u v
open Representation
open GroundTheory.ProfCoh.AdditiveFunction
variable {l : ℕ} {Γ : Type v} [Group Γ] (d : AdditiveFunction.{u} l Γ)
variable {X Y : Type u} [AddCommGroup X] [Module (ZMod l) X] [Finite X]
  [AddCommGroup Y] [Module (ZMod l) Y] [Finite Y]

theorem GroundTheory.ProfCoh.AdditiveFunction.toFun_subrep_congr (ρ : Representation (ZMod l) Γ X) {p q : Submodule (ZMod l) X}
    (h : p = q) (hp : ∀ γ, p ≤ p.comap (ρ γ)) (hq : ∀ γ, q ≤ q.comap (ρ γ)) :
    d.toFun p (ρ.subrepresentation p hp) = d.toFun q (ρ.subrepresentation q hq) := by sorry
