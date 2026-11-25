-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_false_of_dominant
-- name    : GroundTheory.PAdicHodge.WittTilt.false_of_dominant
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:09:48.931573+00:00
-- url     : https://prove2.me/theorems/affc61d3-c612-4dda-9aa5-6515ae97a8f1
-- title:
--   Witt Tilt: false of dominant
-- statement:
--   The Witt Tilt construction uses the false of dominant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BCrisNewtonDom.lean#L44-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BCrisNewtonDom.lean#L44-L105

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonApprox
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonDom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.WittTilt
open _root_.WittVector Laurent ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [CharZero K]
local notation "𝔸" => Localization.Away (p : AInf K p)
variable {ρ : ℝ}
set_option maxHeartbeats 4000000

theorem GroundTheory.PAdicHodge.WittTilt.false_of_dominant (hp0 : ‖(p : K)‖ ≤ ρ) (hρ1 : ρ < 1) {a b : ACris K p} {Na Nb : ℕ}
    {Fa Fb : ℝ}
    (hsa : ∀ N ≥ Na, ∀ c : ACrisZero K p,
      a - algebraMap _ (ACris K p) c ∈ Ideal.span {(p : ACris K p) ^ N} → gn K p ρ (c : 𝔸) = Fa)
    (hsb : ∀ N ≥ Nb, ∀ c : ACrisZero K p,
      b - algebraMap _ (ACris K p) c ∈ Ideal.span {(p : ACris K p) ^ N} → gn K p ρ (c : 𝔸) = Fb)
    (d : ℕ) (x : ℕ → AInf K p)
    (hsum : ∑ i ∈ Finset.range (d + 1),
      algebraMap (AInf K p) (ACris K p) (x i) * a ^ i * b ^ (d - i) = 0)
    {j : ℕ} (hj : j ∈ Finset.range (d + 1))
    (hpos : 0 < gn K p ρ (algebraMap (AInf K p) 𝔸 (x j)) * Fa ^ j * Fb ^ (d - j))
    (hdom : ∀ i ∈ Finset.range (d + 1), i ≠ j →
      gn K p ρ (algebraMap (AInf K p) 𝔸 (x i)) * Fa ^ i * Fb ^ (d - i) <
        gn K p ρ (algebraMap (AInf K p) 𝔸 (x j)) * Fa ^ j * Fb ^ (d - j)) : False := by sorry
