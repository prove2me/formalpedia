-- Prove2me | Theorems.Thm_GlobalTheory_LocSplit_exists_val_eq
-- name    : GlobalTheory.LocSplit.exists_val_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:39:23.659703+00:00
-- url     : https://prove2.me/theorems/339cbbb0-c480-4ec4-9e71-2faa7f2357a5
-- title:
--   Loc Split: exists val eq
-- statement:
--   The Loc Split construction uses the exists val eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIrreducible.lean#L201-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIrreducible.lean#L201-L207

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.MainNotions.S.Loc NumberField IsDedekindDomain ValuativeRel
open GlobalTheory GlobalTheory.LocSplit
variable {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
  {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (ι : F →+* K) (hd : DenseRange ι)
  (hv : ∀ x y : F, valuation K (ι x) ≤ valuation K (ι y) ↔ p.valuation F x ≤ p.valuation F y)
include hd

theorem GlobalTheory.LocSplit.exists_val_eq (x : K) (hx : x ≠ 0) :
    ∃ y : F, y ≠ 0 ∧ valuation K (ι y) = valuation K x := by sorry
