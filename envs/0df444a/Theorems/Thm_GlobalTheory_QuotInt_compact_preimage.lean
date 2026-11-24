-- Prove2me | Theorems.Thm_GlobalTheory_QuotInt_compact_preimage
-- name    : GlobalTheory.QuotInt.compact_preimage
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:53.038826+00:00
-- url     : https://prove2.me/theorems/b46ed77c-bd05-4456-a789-c141773791e6
-- title:
--   Quot Int: compact preimage
-- statement:
--   The Quot Int construction uses the compact preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/QuotientIntegralParabolicUnfolding.lean#L231-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/QuotientIntegralParabolicUnfolding.lean#L231-L255

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsMulLeftInvariantVolGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QuotientIntegralParabolicUnfolding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.QuotInt
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}

theorem GlobalTheory.QuotInt.compact_preimage (hN : IsClosed (N k n c p : Set (GL (n ⊕ Fin c) k))) {C : Set (GL (n ⊕ Fin c) k)}
    (hC : IsCompact C) : ∃ D : Set (GL n k × N k n c p), IsCompact D ∧
      ∀ z : GL n k × N k n c p, embX c z.1 * (z.2 : GL (n ⊕ Fin c) k) ∈ C → z ∈ D := by sorry
