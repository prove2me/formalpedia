-- Prove2me | Theorems.Thm_GlobalTheory_Ex_QStr_exists_roots
-- name    : GlobalTheory.Ex.QStr.exists_roots
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:56:24.259804+00:00
-- url     : https://prove2.me/theorems/89d6b9cf-5674-4f27-96e9-183ea679c491
-- title:
--   QStr: exists roots
-- statement:
--   The QStr construction uses the exists roots property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/DegenerationDataTorsionStructureAlgClosed.lean#L99-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/DegenerationDataTorsionStructureAlgClosed.lean#L99-L111

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

theorem GlobalTheory.Ex.QStr.exists_roots (C : Type) [Field C] [IsAlgClosed C] (k : ℕ) (hk : (k : C) ≠ 0) :
    ∃ ζ : Cˣ, IsPrimitiveRoot ζ k ∧ ∃ e : Multiplicative (ZMod k) →* Cˣ, Function.Injective e ∧
      ∀ u : Cˣ, u ^ k = 1 → ∃ z, e z = u := by sorry
