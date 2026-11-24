-- Prove2me | Theorems.Thm_GlobalTheory_Izumi_exists_dominating_of_residue_map
-- name    : GlobalTheory.Izumi.exists_dominating_of_residue_map
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:23:39.58102+00:00
-- url     : https://prove2.me/theorems/08b6dc39-cdcd-4b07-baad-cb6edb511bbe
-- title:
--   Izumi: exists dominating of residue map
-- statement:
--   The Izumi construction uses the exists dominating of residue map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDominatingLocalDomainEqMulMaximal.lean#L6-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDominatingLocalDomainEqMulMaximal.lean#L6-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDominatingLocalDomainEqMulMaximal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Polynomial
open GlobalTheory GlobalTheory.Izumi

theorem GlobalTheory.Izumi.exists_dominating_of_residue_map {R S : Type} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsDomain S] [IsNoetherianRing S] (j : R →+* S) (hj : Function.Injective j)
    (φ : S →+* ResidueField R) (hφ : ∀ r, φ (j r) = residue R r) (f G : R) (u : S)
    (hu : φ u = 0) (hf : j f = j G * u) :
    ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsLocalRing B) (_ : IsNoetherianRing B)
      (ι : R →+* B), Function.Injective ι ∧ IsLocalHom ι ∧
      (∀ b : B, ∃ r : R, b - ι r ∈ maximalIdeal B) ∧ ∃ u ∈ maximalIdeal B, ι f = ι G * u := by sorry
