-- Prove2me | Theorems.Thm_GlobalTheory_Ex_SymLift_tk_pow
-- name    : GlobalTheory.Ex.SymLift.tk_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:56:33.466835+00:00
-- url     : https://prove2.me/theorems/7b034ca2-a5a1-4fdb-a99b-3fa2e4ced73d
-- title:
--   Sym Lift: tk pow
-- statement:
--   The Sym Lift construction uses the tk pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/NormalisingFactor.lean#L29-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/NormalisingFactor.lean#L29-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataPsiQuadraticGeneratorsLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormalisingFactor
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
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.SymLift
variable {O : Type} [CommRing O] (N : NumD O)

theorem GlobalTheory.Ex.SymLift.tk_pow {k : ℕ} (p p' : N.QT k) :
    N.tk p p' ^ k = N.τ p.1.1.toAdd p'.1.1.toAdd *
      (cubN N.θ k 1 p.1.2.b (p'.1.2.b ^ k) * cubN N.θ k 1 p'.1.2.b p.1.2.b ^ k) := by sorry
