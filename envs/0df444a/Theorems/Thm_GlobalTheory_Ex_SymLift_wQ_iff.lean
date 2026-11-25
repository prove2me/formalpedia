-- Prove2me | Theorems.Thm_GlobalTheory_Ex_SymLift_wQ_iff
-- name    : GlobalTheory.Ex.SymLift.wQ_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:51:58.535827+00:00
-- url     : https://prove2.me/theorems/5828e49f-8610-4cb9-9100-81b272ba2ae3
-- title:
--   Sym Lift: w Q iff
-- statement:
--   The Sym Lift construction uses the w Q iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/NormalisingFactor.lean#L51-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/NormalisingFactor.lean#L51-L69

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

theorem GlobalTheory.Ex.SymLift.wQ_iff {k : ℕ} (hk : Odd k) (p : N.QT k) (w : Oˣ) :
    w = N.wQ p ↔ (w ^ 2 * dbl N.θ N.σ p.1.2.b ^ k = N.tk p p ∧
      w ^ k = N.ψ p.1.1.toAdd * mulq N.θ N.σ k p.1.2.b) := by sorry
