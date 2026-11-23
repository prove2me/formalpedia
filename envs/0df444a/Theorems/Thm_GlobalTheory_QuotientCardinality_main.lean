-- Prove2me | Theorems.Thm_GlobalTheory_QuotientCardinality_main
-- name    : GlobalTheory.QuotientCardinality.main
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:24:44.797032+00:00
-- url     : https://prove2.me/theorems/caa29fd5-eca4-4b14-b550-e22cd5cb86b9
-- title:
--   Quotient Cardinality: main
-- statement:
--   The Quotient Cardinality construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ImportsBis.lean#L7-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ImportsBis.lean#L7-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsBis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.QuotientCardinality
open ValuativeRel

theorem GlobalTheory.QuotientCardinality.main : ∀ {F : Type} [inst : Field F] [inst_1 : ValuativeRel F] [inst_2 : TopologicalSpace F] [IsNonarchimedeanLocalField F] {ϖ : ↥(Valuation.integer (ValuativeRel.valuation F))}, Irreducible ϖ → ∀ {a : ℤ} {m : ℕ} {u v : (↥(Valuation.integer (ValuativeRel.valuation F)))ˣ}, (↑ϖ : F) ^ a * (↑(↑u : ↥(Valuation.integer (ValuativeRel.valuation F))) : F) * (↑(↑v : ↥(Valuation.integer (ValuativeRel.valuation F))) : F) = (↑ϖ : F) ^ m → a = (↑m : ℤ) := by sorry
