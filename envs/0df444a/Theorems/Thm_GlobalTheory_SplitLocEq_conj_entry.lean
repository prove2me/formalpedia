-- Prove2me | Theorems.Thm_GlobalTheory_SplitLocEq_conj_entry
-- name    : GlobalTheory.SplitLocEq.conj_entry
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:21:22.781839+00:00
-- url     : https://prove2.me/theorems/761277e4-15fb-432e-a3ca-29ffba5534ce
-- title:
--   Split Loc Eq: conj entry
-- statement:
--   The Split Loc Eq construction uses the conj entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/EqZeroOfSupportedAtSplit.lean#L11-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/EqZeroOfSupportedAtSplit.lean#L11-L23

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CmFieldAdeleSplitPlaceSupportIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EqZeroOfSupportedAtSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 TensorProduct
open GlobalTheory GlobalTheory.SplitLocEq
open NumberField IsDedekindDomain TensorProduct

theorem GlobalTheory.SplitLocEq.conj_entry {L : Type} [Field L] [NumberField L] [IsCMField L]
    {n : ℕ} (x : _root_.ReciprocityTheory.Aut.GA L n) (i j : Fin n) :
    _root_.ReciprocityTheory.Aut.conjAL L ((x.1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) i j) =
      (((x⁻¹ : _root_.ReciprocityTheory.Aut.GA L n).1 : GL (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) j i := by sorry
