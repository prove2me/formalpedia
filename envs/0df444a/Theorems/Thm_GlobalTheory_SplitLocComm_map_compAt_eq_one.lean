-- Prove2me | Theorems.Thm_GlobalTheory_SplitLocComm_map_compAt_eq_one
-- name    : GlobalTheory.SplitLocComm.map_compAt_eq_one
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:23:10.255807+00:00
-- url     : https://prove2.me/theorems/5b18beb3-8346-4679-af8d-9378471024da
-- title:
--   Split Loc Comm: map comp At eq one
-- statement:
--   The Split Loc Comm construction uses the map comp At eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/CommuteOfLocEqOne.lean#L16-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/CommuteOfLocEqOne.lean#L16-L39

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EqZeroOfCompAtEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsRealAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CommuteOfLocEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
noncomputable section
open GlobalTheory GlobalTheory.SplitLocComm
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
local notation3 "L⁺" => maximalRealSubfield L

theorem GlobalTheory.SplitLocComm.map_compAt_eq_one {n : ℕ} (s : SplitPlace L) (x : GA L n) (hx : s.loc n x = 1) :
    (x.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L s.v) = 1 := by sorry
