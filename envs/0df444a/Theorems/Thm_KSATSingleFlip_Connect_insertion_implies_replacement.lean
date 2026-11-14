-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_insertion_implies_replacement
-- name    : KSATSingleFlip.Connect.insertion_implies_replacement
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:36:25.054767+00:00
-- url     : https://prove2.me/theorems/fb8d91e2-acf8-4894-8fc0-dbb32f427f87
-- title:
--   Insertion sensitivity bounds one-clause replacement
-- statement:
--   If inserting one element at any position in a marked-clause list changes an observable by at most L, then changing any single coordinate of a fixed-length list changes it by at most 2L. This is the deletion-and-insertion step needed for the bounded-differences estimate in Lemma 2.6.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Lemma 2.6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Mathlib
set_option autoImplicit false

theorem KSATSingleFlip.Connect.insertion_implies_replacement {A : Type} (j : ℕ) (F : List A → ℝ) (L : ℝ)
    (hins : ∀ (xs : List A) (i : ℕ) (a : A), |F (xs.insertIdx i a) - F xs| ≤ L)
    (x : Fin j → A) (i : Fin j) (a : A) :
    |F (List.ofFn x) - F (List.ofFn (Function.update x i a))| ≤ 2*L := by sorry
