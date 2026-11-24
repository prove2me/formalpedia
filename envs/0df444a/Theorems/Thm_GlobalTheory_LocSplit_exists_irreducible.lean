-- Prove2me | Theorems.Thm_GlobalTheory_LocSplit_exists_irreducible
-- name    : GlobalTheory.LocSplit.exists_irreducible
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:14:19.917799+00:00
-- url     : https://prove2.me/theorems/665d4aef-cfec-4178-8e6a-9f99490d4142
-- title:
--   Loc Split: exists irreducible
-- statement:
--   The Loc Split construction uses the exists irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIrreducible.lean#L211-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIrreducible.lean#L211-L246

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

theorem GlobalTheory.LocSplit.exists_irreducible (g : F) (hg : p.valuation F g = WithZero.exp (-1 : ℤ)) :
    ∃ q : 𝒪[K], Irreducible q ∧ (q : K) = ι g := by sorry
