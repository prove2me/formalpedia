-- Prove2me | Theorems.Thm_GlobalTheory_FitSquare_relations_mem
-- name    : GlobalTheory.FitSquare.relations_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:08:45.970285+00:00
-- url     : https://prove2.me/theorems/31d4546e-87af-4948-b2b8-ee19a07b934a
-- title:
--   Fit Square: relations mem
-- statement:
--   The Fit Square construction uses the relations mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DetMemSpanAdjugate.lean#L64-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DetMemSpanAdjugate.lean#L64-L153

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DetMemSpanAdjugate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.FitSquare
variable {R : Type} [CommRing R]
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
open Matrix
variable {R : Type} [CommRing R]
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

theorem GlobalTheory.FitSquare.relations_mem {M : Type} [AddCommGroup M] [Module R M]
    (π : (n → R) →ₗ[R] M) (hπ : Function.Surjective π) (Φ : Matrix n n R)
    (hΦ : ∀ y, π y = 0 → ∃ z, Φ *ᵥ z = y)
    (q : (m → R) →ₗ[R] M) (hq : Function.Surjective q) (T : Matrix m m R)
    (hT : ∀ y, q (T *ᵥ y) = 0) :
    T.det ∈ Ideal.span {Φ.det} ∧ (Nonempty n → ∀ i j, T.adjugate i j ∈
      Ideal.span (Set.range fun p : n × n => Φ.adjugate p.1 p.2)) := by sorry
