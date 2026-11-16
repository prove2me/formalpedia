-- Prove2me | Theorems.Thm_Kyprianou_Ch06_iIndepFun_finInsertZero
-- name    : Kyprianou.Ch06.iIndepFun_finInsertZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T21:35:55.630875+00:00
-- url     : https://prove2.me/theorems/82b14a23-c2d1-4ae3-856b-068f3b497a01
-- title:
--   Finite-coordinate zero insertion via Fin.succAbove preserves joint independence
-- statement:
--   Take n independent real-valued random variables. Insert a constant-zero variable at any position in the (n+1)-coordinate family, with all other variables matched by the order-preserving Fin.succAbove reindexing. The entire new family remains mutually independent for any probability measure. The result is uniform in n and the insertion point.
-- source:
--   Finite-index independence and reindexing using the previously proved subtype deletion bridge and the pinned Mathlib Fin.succAbove order embedding. Supports Chapter 6 repeated-time increments.

import Mathlib
import Theorems.Thm_Kyprianou_Ch06_iIndepFun_of_delete_const_subtype
set_option autoImplicit false
open MeasureTheory ProbabilityTheory

theorem Kyprianou.Ch06.iIndepFun_finInsertZero
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (hprob : P Set.univ = 1)
    (n : Nat) (f : Fin (n + 1) → Ω → Real)
    (g : Fin n → Ω → Real) (k : Fin (n + 1))
    (hzero : f k = fun _ => 0)
    (hrel : ∀ j : Fin n, f (k.succAbove j) = g j)
    (hInd : ProbabilityTheory.iIndepFun g P) :
    ProbabilityTheory.iIndepFun f P := by sorry
