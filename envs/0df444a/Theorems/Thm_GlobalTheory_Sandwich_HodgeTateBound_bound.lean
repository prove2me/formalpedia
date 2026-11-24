-- Prove2me | Theorems.Thm_GlobalTheory_Sandwich_HodgeTateBound_bound
-- name    : GlobalTheory.Sandwich.HodgeTateBound.bound
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:45:28.75862+00:00
-- url     : https://prove2.me/theorems/7b4f95ae-cefd-4978-b5a1-7236fdea05f2
-- title:
--   Hodge Tate Bound: bound
-- statement:
--   The Hodge Tate Bound construction uses the bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmulMemRange.lean#L154-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmulMemRange.lean#L154-L258

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_XiMulNu
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FontaineAinfLocalDomainXiAdicOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmulMemRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh.Up GlobalTheory.Sandwich Matrix
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.Sandwich.HodgeTateBound
open Matrix

theorem GlobalTheory.Sandwich.HodgeTateBound.bound : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C]
    [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O →
    ∀ ε : PreTilt O p, IsPrimitiveRoot (_root_.GlobalTheory.Sandwich.root ε).untilt p →
    ∀ (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ], ∀ (h : ℕ) (D : _root_.GlobalTheory.Sandwich.Datum ε h Λ),
    D.F * D.G =
        _root_.GlobalTheory.Sandwich.mu ε • (1 : Matrix (Fin h) (Fin h) (_root_.GlobalTheory.Sandwich.Ainf p O)) ∧
      LinearMap.range D.al ≤ D.Fil ∧
      D.Lie ≤ LinearMap.ker D.al ∧
      (∀ f ∈ D.Fil, WittVector.fontaineTheta O p (_root_.GlobalTheory.Sandwich.nu ε) • f ∈
        LinearMap.range D.al) ∧
      (∀ t ∈ LinearMap.ker D.al,
        WittVector.fontaineTheta O p (_root_.GlobalTheory.Sandwich.nu ε) • t ∈ D.Lie) ∧
      (∀ τ : Λ →+* O, (D.Tsub τ).map D.al ≤
          D.Fil ⊓ D.Hsub τ ∧
        (D.Hsub τ).map D.bb ≤
          D.Lie ⊓ D.Tsub τ ∧
        D.Lie ⊓ D.Tsub τ ≤
          D.W τ) := by sorry
