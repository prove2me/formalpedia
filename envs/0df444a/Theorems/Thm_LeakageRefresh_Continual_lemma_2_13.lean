-- Prove2me | Theorems.Thm_LeakageRefresh_Continual_lemma_2_13
-- name    : LeakageRefresh.Continual.lemma_2_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:08:59.761893+00:00
-- url     : https://prove2.me/theorems/149c70f0-78f4-4ce7-9be4-edee5b596125
-- title:
--   Lemma 2.13 — basic nuclear-norm bounds: a norm, $\|F\|_2\le\|F\|_*$, $\|\sum a_jb_j^T\|_*\le\sum\|a_j\|_2\|b_j\|_2$, $\|ab^T\|_*=\|a\|_2\|b\|_2$
-- statement:
--   Let $n\ge2$ and consider real tables $F:U_L\times U_R\to\mathbb R$ with the probability-normalized norms. Then $\|\cdot\|_*$ is a norm on these tables, and for every table $F$
--   $$\|F\|_2\le\|F\|_*. \tag{2.4}$$
--   For every $m\ge0$ and functions $a_j:U_L\to\mathbb R$, $b_j:U_R\to\mathbb R$ ($j=1,\dots,m$),
--   $$\Big\|\sum_j a_j b_j^T\Big\|_*\le\sum_j\|a_j\|_2\|b_j\|_2, \tag{2.5}$$
--   and for every $a:U_L\to\mathbb R$, $b:U_R\to\mathbb R$, $\|a b^T\|_*=\|a\|_2\|b\|_2$ (2.6).
--
--   These are the facts that make the nuclear norm the cost measure of the hybrid argument: products of local approximations are bounded through (2.5).
--
--   Differences from the source:
--   - encoding: "$\|\cdot\|_*$ is a norm" → four clauses: $\|F\|_*\ge0$; $\|F\|_*=0\iff F=0$; $\|cF\|_*=|c|\|F\|_*$; $\|F+G\|_*\le\|F\|_*+\|G\|_*$; reason: the norm axioms written out
--   - encoding: $\|F\|_*$ as the sum of singular coefficients of an orthonormal expansion (Def. 2.11) → `nuclearNorm`: $(|U_L||U_R|)^{-1/2}$ times the sum of square roots of the eigenvalues of $F^TF$; reason: the paper's own identification of the normalized singular coefficients with scaled ordinary singular values (p. 17)
-- source:
--   Dziembowski, Faust, Leakage-Resilient Computation via Matrix Refreshing, arXiv:2611.04876 (sha256 fdbb2454…), p. 20, Lemma 2.13

import Mathlib
import Definitions.Def_LeakageRefresh_Continual_Encoding
import Definitions.Def_LeakageRefresh_Continual_Tables

namespace LeakageRefresh.Continual

/-- **Lemma 2.13 (Basic nuclear-norm bounds).** On the real tables on `U_L × U_R`, `‖·‖_*` is a
norm (nonnegative, zero exactly at `0`, absolutely homogeneous, subadditive);
(2.4) `‖F‖₂ ≤ ‖F‖_*`; (2.5) `‖∑ⱼ aⱼ bⱼᵀ‖_* ≤ ∑ⱼ ‖aⱼ‖₂ ‖bⱼ‖₂` for every `m ≥ 0`;
(2.6) `‖a bᵀ‖_* = ‖a‖₂ ‖b‖₂`. -/
theorem lemma_2_13 (n : ℕ) (hn : 2 ≤ n) :
    (∀ F : Table (UL n) (UR n), 0 ≤ nuclearNorm F) ∧
    (∀ F : Table (UL n) (UR n), nuclearNorm F = 0 ↔ F = 0) ∧
    (∀ (c : ℝ) (F : Table (UL n) (UR n)), nuclearNorm (c • F) = |c| * nuclearNorm F) ∧
    (∀ F G : Table (UL n) (UR n), nuclearNorm (F + G) ≤ nuclearNorm F + nuclearNorm G) ∧
    (∀ F : Table (UL n) (UR n), tableL2 F ≤ nuclearNorm F) ∧
    (∀ (m : ℕ) (a : Fin m → UL n → ℝ) (b : Fin m → UR n → ℝ),
      nuclearNorm (fun ℓ r => ∑ j, a j ℓ * b j r) ≤ ∑ j, l2 (a j) * l2 (b j)) ∧
    (∀ (a : UL n → ℝ) (b : UR n → ℝ), nuclearNorm (outer a b) = l2 a * l2 b) := by sorry

end LeakageRefresh.Continual
