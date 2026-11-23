-- Prove2me | Theorems.Thm_GlobalTheory_Ex_QStr_chr_eq
-- name    : GlobalTheory.Ex.QStr.chr_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:56:53.673818+00:00
-- url     : https://prove2.me/theorems/1eeb5060-0632-4e01-a76e-34e08ede0d39
-- title:
--   QStr: chr eq
-- statement:
--   The QStr construction uses the chr eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/DegenerationDataTorsionStructureAlgClosed.lean#L73-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/DegenerationDataTorsionStructureAlgClosed.lean#L73-L77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.QStr
variable {X U ι : Type} [AddCommGroup X] [CommGroup U] [Fintype ι] (v : Module.Basis ι ℤ X)

theorem GlobalTheory.Ex.QStr.chr_eq (t : Multiplicative X →* U) : chr v (fun i => t (Multiplicative.ofAdd (v i))) = t := by sorry
