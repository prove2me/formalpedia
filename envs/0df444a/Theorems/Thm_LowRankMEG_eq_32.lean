-- Prove2me | Theorems.Thm_LowRankMEG_eq_32
-- name    : LowRankMEG.eq_32
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:51:16.871866+00:00
-- url     : https://prove2.me/theorems/d4dd9aed-3444-4ebb-aaf0-fd44c5239ffc
-- title:
--   (32) — the descent inequality
-- statement:
--   Let $X^*$ be optimal, and let $X,Z\in\mathcal S_n$ be positive definite. Then
--   $$
--   \langle\nabla f(X),Z-X\rangle\ge f(X^*)-f(X)-\beta B(Z,X).
--   $$
--   On the page $X=X_t$ and $Z=Z_{t+1}$ is the exact update of $X_t$. The inequality follows from smoothness and (3), and it enters the proof of Lemma 5.
--
--   Differences from the source:
--   - generalization: Z_{t+1}, the exact update (6) of X_t → Z any positive definite point of 𝒮_n; reason: the update is such a point, and the derivation uses nothing else about it
--   - encoding: the gradient ∇f → a map grad tied to f by HasFDerivAt at symmetric matrices (Setting.hasGrad); reason: Lean needs ∇f as data; same instances
-- source:
--   Garber & Kaplan, On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for Low-Rank Matrix Optimization, arXiv:2012.10469v2, Eq. (32), p.19

import Mathlib
import Definitions.Def_LowRankMEG_Setting
import Definitions.Def_LowRankMEG_IsOptimal
import Definitions.Def_PSDPolyApprox_densityMatrices
import Definitions.Def_LowRankMEG_bregman

namespace LowRankMEG

/-- **Eq. (32)**: `⟨∇f(X_t), Z_{t+1} − X_t⟩ ≥ f(X*) − f(X_t) − βB(Z_{t+1}, X_t)`.
Garber & Kaplan, *On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for
Low-Rank Matrix Optimization*, arXiv:2012.10469v2, Eq. (32), p.19, in the proof of Lemma 5.

**Formalization Note.** `Z` is any positive definite point of `𝒮_n`; the page's `Z_{t+1}`, the update (6) of `X_t`,
is one. -/
theorem eq_32 {n : ℕ} {f : Matrix (Fin n) (Fin n) ℝ → ℝ}
    {grad : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ} {β : ℝ}
    (hS : Setting f grad β)
    {Xs X Z : Matrix (Fin n) (Fin n) ℝ} (hopt : IsOptimal f Xs)
    (hX : X ∈ PSDPolyApprox.densityMatrices n) (hXpd : X.PosDef) (hZ : Z ∈ PSDPolyApprox.densityMatrices n) (hZpd : Z.PosDef) :
    f Xs - f X - β * bregman Z X ≤ (grad X * (Z - X)).trace := by sorry

end LowRankMEG
