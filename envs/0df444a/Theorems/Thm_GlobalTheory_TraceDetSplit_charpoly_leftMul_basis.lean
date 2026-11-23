-- Prove2me | Theorems.Thm_GlobalTheory_TraceDetSplit_charpoly_leftMul_basis
-- name    : GlobalTheory.TraceDetSplit.charpoly_leftMul_basis
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:05:27.869917+00:00
-- url     : https://prove2.me/theorems/3fe5378a-7712-4ac5-ac06-91ed079ca47a
-- title:
--   Trace Det Split: charpoly left Mul basis
-- statement:
--   The Trace Det Split construction uses the charpoly left Mul basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyLeftMulBasis.lean#L68-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyLeftMulBasis.lean#L68-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyLeftMulBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.TraceDetSplit

theorem GlobalTheory.TraceDetSplit.charpoly_leftMul_basis {E A : Type} [Field E] [CommRing A] [Algebra E A]
    [Module.Finite E A] {n : ℕ} (g : A) (w : Module.Basis (Fin n) E A) :
    (Algebra.leftMulMatrix w g).charpoly = (LinearMap.mulLeft E g).charpoly := by sorry
