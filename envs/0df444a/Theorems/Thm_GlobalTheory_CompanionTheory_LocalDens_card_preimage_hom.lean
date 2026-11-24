-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_card_preimage_hom
-- name    : GlobalTheory.CompanionTheory.LocalDens.card_preimage_hom
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:52:24.937051+00:00
-- url     : https://prove2.me/theorems/2aa3ceec-b04e-49fd-b63b-1346cd18ae21
-- title:
--   Local Dens: card preimage hom
-- statement:
--   The Local Dens construction uses the card preimage hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardPreimageHom.lean#L190-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardPreimageHom.lean#L190-L211

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardPreimageHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LocalDens
open PositivityTheory.PfSWUS.Loc
variable {R : Type} [CommRing R]

theorem GlobalTheory.CompanionTheory.LocalDens.card_preimage_hom {A B : Type} [AddCommGroup A] [AddCommGroup B] [Finite A] [Finite B] (f : A →+ B)
    (hf : Function.Surjective f) (U : Set B) :
    Nat.card (f ⁻¹' U) * Nat.card B = Nat.card U * Nat.card A := by sorry
