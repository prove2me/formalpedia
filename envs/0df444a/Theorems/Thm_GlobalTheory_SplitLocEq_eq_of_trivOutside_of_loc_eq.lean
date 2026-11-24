-- Prove2me | Theorems.Thm_GlobalTheory_SplitLocEq_eq_of_trivOutside_of_loc_eq
-- name    : GlobalTheory.SplitLocEq.eq_of_trivOutside_of_loc_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:21:40.012854+00:00
-- url     : https://prove2.me/theorems/ce971cbe-decd-499e-847c-01680ca56a4d
-- title:
--   Split Loc Eq: eq of triv Outside of loc eq
-- statement:
--   The Split Loc Eq construction uses the eq of triv Outside of loc eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/EqZeroOfSupportedAtSplit.lean#L91-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/EqZeroOfSupportedAtSplit.lean#L91-L121

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

theorem GlobalTheory.SplitLocEq.eq_of_trivOutside_of_loc_eq : ∀ (L : Type) [Field L] [NumberField L]
    [IsCMField L] (n : ℕ) (s : _root_.ReciprocityTheory.Aut.SplitPlace L) (x y : _root_.Formalism.AUTREP.GAf L n),
    _root_.ReciprocityTheory.Aut.TrivOutside {s.v} x → _root_.ReciprocityTheory.Aut.TrivOutside {s.v} y → s.loc n x = s.loc n y → x = y := by sorry
