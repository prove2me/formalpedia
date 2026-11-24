-- Prove2me | Theorems.Thm_GlobalTheory_AdSplit_exists_prod_equiv
-- name    : GlobalTheory.AdSplit.exists_prod_equiv
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:54:22.275814+00:00
-- url     : https://prove2.me/theorems/b363ca5f-eee7-4352-9fbc-4c3989fd42b9
-- title:
--   Ad Split: exists prod equiv
-- statement:
--   The Ad Split construction uses the exists prod equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsAdeleRingTensorEquivInfiniteProdFinite.lean#L9-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsAdeleRingTensorEquivInfiniteProdFinite.lean#L9-L110

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsAdeleRingTensorEquivInfiniteProdFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
open GlobalTheory GlobalTheory.AdSplit

theorem GlobalTheory.AdSplit.exists_prod_equiv (F E A B : Type) [CommRing F] [CommRing E] [Algebra F E]
    [CommRing A] [Algebra F A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [Algebra F B] [TopologicalSpace B] [IsTopologicalRing B] :
    letI : TopologicalSpace ((A × B) ⊗[F] E) := moduleTopology (A × B) ((A × B) ⊗[F] E)
    letI : TopologicalSpace (B ⊗[F] E) := moduleTopology B (B ⊗[F] E)
    letI : TopologicalSpace (A ⊗[F] E) := moduleTopology A (A ⊗[F] E)
    ∃ e : ((A × B) ⊗[F] E) ≃+* (A ⊗[F] E) × (B ⊗[F] E),
      (∀ z, (e z).1 = Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z ∧
        (e z).2 = Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z) ∧
      Continuous e ∧ Continuous e.symm := by sorry
