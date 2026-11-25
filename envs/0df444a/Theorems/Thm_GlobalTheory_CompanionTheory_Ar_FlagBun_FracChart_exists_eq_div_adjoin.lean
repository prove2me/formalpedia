-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_FlagBun_FracChart_exists_eq_div_adjoin
-- name    : GlobalTheory.CompanionTheory.Ar.FlagBun.FracChart.exists_eq_div_adjoin
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:59:15.101822+00:00
-- url     : https://prove2.me/theorems/66d4cb8e-640e-4244-ab3d-0d31b7523eab
-- title:
--   Frac Chart: exists eq div adjoin
-- statement:
--   The Frac Chart construction uses the exists eq div adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/FunctionFieldRatioGenerators.lean#L7-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/FunctionFieldRatioGenerators.lean#L7-L88

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_CoordTieCompEquiv
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_FunctionFieldRatioGenerators
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.FracChart

theorem GlobalTheory.CompanionTheory.Ar.FlagBun.FracChart.exists_eq_div_adjoin (X : Scheme.{0}) (Ω : Type) [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω) (c : κ)
    (hT : CoordTie ℤ ξ x) (hc : x c ≠ 0) (a : Ω) :
    ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c),
      ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c), h ≠ 0 ∧ a = g / h := by sorry
