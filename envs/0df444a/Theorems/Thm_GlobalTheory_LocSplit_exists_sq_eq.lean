-- Prove2me | Theorems.Thm_GlobalTheory_LocSplit_exists_sq_eq
-- name    : GlobalTheory.LocSplit.exists_sq_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:14:28.689502+00:00
-- url     : https://prove2.me/theorems/227a810c-0641-4673-a6f2-32702b053f4b
-- title:
--   Loc Split: exists sq eq
-- statement:
--   The Loc Split construction uses the exists sq eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIrreducible.lean#L250-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIrreducible.lean#L250-L276

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
include hd hv

theorem GlobalTheory.LocSplit.exists_sq_eq (a : 𝓞 F) (ha : ∀ n : ℕ, ∃ m : ℤ, a - (m : 𝓞 F) ^ 2 ∈ p.asIdeal ^ n) :
    ∃ β : K, β ^ 2 = ι a := by sorry
