-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ringHom_iterate_frobeniusEquiv_symm
-- name    : GroundTheory.PAdicHodge.ringHom_iterate_frobeniusEquiv_symm
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:10:35.473411+00:00
-- url     : https://prove2.me/theorems/a3aad273-0791-451b-9407-eb11de7dc971
-- title:
--   PAdic Hodge: ring Hom iterate frobenius Equiv symm
-- statement:
--   The PAdic Hodge construction uses the ring Hom iterate frobenius Equiv symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltGaloisCorr.lean#L25-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltGaloisCorr.lean#L25-L31

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGalois
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGaloisCorr
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
variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪K♭" => PreTilt (normInteger K) p
local notation "𝒪C♭" => PreTilt (normInteger C) p

theorem GroundTheory.PAdicHodge.ringHom_iterate_frobeniusEquiv_symm {R S : Type*} [CommRing R] [CommRing S] [CharP R p]
    [CharP S p] [PerfectRing R p] [PerfectRing S p] (f : R →+* S) (x : R) (n : ℕ) :
    f ((frobeniusEquiv R p).symm^[n] x) = (frobeniusEquiv S p).symm^[n] (f x) := by sorry
