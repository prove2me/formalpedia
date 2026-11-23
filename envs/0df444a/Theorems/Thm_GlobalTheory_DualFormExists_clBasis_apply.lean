-- Prove2me | Theorems.Thm_GlobalTheory_DualFormExists_clBasis_apply
-- name    : GlobalTheory.DualFormExists.clBasis_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:00:13.825056+00:00
-- url     : https://prove2.me/theorems/e744febc-dc5e-4e51-a924-f78fcc5d1e60
-- title:
--   Dual Form Exists: cl Basis apply
-- statement:
--   The Dual Form Exists construction uses the cl Basis apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DualFormExistsUnique.lean#L102-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DualFormExistsUnique.lean#L102-L103

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualFormExistsUnique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum
noncomputable section
open GlobalTheory GlobalTheory.DualFormExists
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.DualFormExists.clBasis_apply (ξ : E) (hξ : ξ ≠ 0) (i) : clBasis ξ hξ i = riemannCl ξ (Module.finBasis ℚ E i) := by sorry
