-- Prove2me | Theorems.Thm_MomentSearch_Supplement_jl_near_orthogonal_labels
-- name    : MomentSearch.Supplement.jl_near_orthogonal_labels
-- status  : Proved
-- author  : @nmegow
-- created : 2026-11-21T01:17:15.506947+00:00
-- url     : https://prove2.me/theorems/194575bf-0d7a-4b1d-a679-f5254a4a789a
-- title:
--   Near-orthogonal labels for interval indices
-- statement:
--   For $n\ge2$ and $0<\eta<1$, there exist $n$ real vectors whose Gram matrix is entrywise within $\eta$ of the identity, in dimension at most $A\log_2(n)/\eta^2$ for one absolute constant $A$.
-- source:
--   Megow, Stein, Verschae, Distributionally Robust Search: The Power of Information and the Limits of Moments, arXiv:2611.04559 (held version, sha256 fbfa4b43350dfaea073a9c0a9a0850a9955ea82082a7163a2db90cc48b9339e3), Theorem 27, p.35 (PDF p.37); construction preceding Theorem 27.

import Mathlib

theorem MomentSearch.Supplement.jl_near_orthogonal_labels : ∃ A : ℝ, 0 < A ∧ ∀ (n : ℕ), 2 ≤ n → ∀ η : ℝ, 0 < η → η < 1 →
    ∃ R : ℕ, (R : ℝ) ≤ A * Real.logb 2 n / η^2 ∧
      ∃ g : Fin n → Fin R → ℝ, ∀ a b,
        |(∑ s, g a s * g b s) - (if a = b then 1 else 0)| ≤ η := by sorry
