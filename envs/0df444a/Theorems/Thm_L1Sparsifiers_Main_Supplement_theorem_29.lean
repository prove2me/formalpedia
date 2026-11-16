-- Prove2me | Theorems.Thm_L1Sparsifiers_Main_Supplement_theorem_29
-- name    : L1Sparsifiers.Main.Supplement.theorem_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:18:39.836786+00:00
-- url     : https://prove2.me/theorems/d5954ffc-4904-411b-8f1e-b3c58076e2d0
-- title:
--   Theorem 29 — $\mathbb P_{x\sim\{-1,1\}^m}[\sum_i x_iA_i\succeq0]\ge e^{-2n}$ for PSD $A_i$
-- statement:
--   Let $A_1,\dots,A_m\in\mathbb R^{n\times n}$ be positive semidefinite. If $x$ is drawn uniformly from the $2^m$ sign vectors $\{-1,1\}^m$, then
--   $$\mathbb P_{x\sim\{-1,1\}^m}\Big[\sum_{i=1}^m x_iA_i\succeq0\Big]\ \ge\ e^{-2n}.$$
--   The bound depends only on the matrix size $n$, not on the number $m$ of matrices; it holds for every $m,n\ge0$.
--
--   This is the tight spectral positivity bound behind the paper's alternative proof of linear-size spectral sparsifiers; Corollary 30 extends it to any independent symmetric coordinates.
--
--   **Formalization Note** The probability is the uniform average `PSDPolyApprox.expect` over `Fin m → ℤˣ` of the indicator of the event, with each sign cast to $\mathbb R$; $\succeq0$ is `Matrix.PosSemidef`.
--
--   Differences from the source:
--   - reading: A₁, …, A_m ⊆ ℝ^{n×n} → A : Fin m → Matrix (Fin n) (Fin n) ℝ (each Aᵢ ∈ ℝ^{n×n}); reason: '⊆' is a typo for '∈': the Aᵢ are matrices, as 'Aᵢ ⪰ 0' in the same sentence shows
--   - encoding: P_{x∼{−1,1}^m}[E] → expect of the 0/1 indicator of E over PSDPolyApprox.Cube m = Fin m → ℤˣ; reason: the uniform probability on the 2^m sign vectors is the uniform average of the indicator
-- source:
--   Victor Reis, Thomas Rothvoss, Linear-size ℓ1 sparsifiers, STOC 2027 submission #162 (October 2026; PDF SHA-256 5137e7dee3cd303bd508f90f5f42c955632af5dc2ec978d9ef575bae4ce23710), §7.1, Theorem 29, p.19

import Mathlib
import Definitions.Def_PSDPolyApprox_Cube
import Definitions.Def_PSDPolyApprox_expect

namespace L1Sparsifiers.Main.Supplement

open PSDPolyApprox

/-- **Theorem 29** (Reis–Rothvoss, STOC 2027 submission #162, §7.1, p.19).
"Let A₁, …, A_m ⊆ ℝ^{n×n} be matrices with Aᵢ ⪰ 0 for all i ∈ [m]. Then
P_{x∼{−1,1}^m}[∑_{i=1}^m xᵢ Aᵢ ⪰ 0] ≥ e^{−2n}."

The `⊆` of the source is read as `∈`. `x` is uniform on the `2^m` sign vectors
(`PSDPolyApprox.Cube m`, coordinates `±1 ∈ ℤˣ` cast to `ℝ`), so the probability is the uniform
average `expect` of the indicator of the event `∑ xᵢ Aᵢ ⪰ 0` (`Matrix.PosSemidef`). Every `m, n`,
including `0`, is allowed. -/
theorem theorem_29 {m n : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i, (A i).PosSemidef) :
    Real.exp (-2 * n) ≤
      expect (fun x : Cube m =>
        by classical exact if (∑ i, ((x i : ℤ) : ℝ) • A i).PosSemidef then (1 : ℝ) else 0) := by sorry

end L1Sparsifiers.Main.Supplement
