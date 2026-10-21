-- Prove2me | Theorems.Thm_ModernConvex_Ellipsoids_lowner_fritz_john
-- name    : ModernConvex.Ellipsoids.lowner_fritz_john
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:34:53.23605+00:00
-- url     : https://prove2.me/theorems/6a232b38-e29f-47b6-b590-dc4d093f1f29
-- title:
--   Theorem 4.9.1 — Löwner–Fritz John: unique extremal ellipsoids of a solid, within factor n (√n if symmetric)
-- statement:
--   Let $S\subset\mathbb R^n$ be a **solid**, i.e. a closed and bounded convex set with nonempty interior. Volumes are normalized, so the unit Euclidean ball has volume $1$. For a full-dimensional ellipsoid $E=\{Au+c \mid u^Tu\le1\}$ ($A$ square, $\operatorname{Det}A\neq0$) and $r>0$, the **concentric ellipsoid $r$ times larger** (in linear sizes) is $\{(rA)u+c \mid u^Tu\le1\}$.
--
--   1. There is exactly one largest-volume full-dimensional ellipsoid $E_{\rm in}$ contained in $S$. If $E_{\rm in}=\{Au+c \mid u^Tu\le 1\}$, then
--   $$S\subseteq\{(nA)u+c \mid u^Tu\le1\}.$$
--   If $S$ is central-symmetric, then already $S\subseteq\{(\sqrt n\,A)u+c \mid u^Tu\le1\}$.
--   2. There is exactly one smallest-volume full-dimensional ellipsoid $E_{\rm out}$ containing $S$. If $E_{\rm out}=\{Au+c \mid u^Tu\le 1\}$, then
--   $$\{(\tfrac1n A)u+c \mid u^Tu\le1\}\subseteq S.$$
--   If $S$ is central-symmetric, then already $\{(\tfrac1{\sqrt n}A)u+c \mid u^Tu\le1\}\subseteq S$.
--
--   This is the classical existence, uniqueness and rounding theorem for extremal ellipsoids. In §4.9 it supplies the "true" smallest-volume ellipsoid against which the semidefinite approximations are measured.
--
--   **Formalization Note** "Exists and is uniquely defined" is `∃!` over sets $E\subseteq\mathbb R^n$ that are largest (resp. smallest) volume full-dimensional ellipsoids. The rounding claims are stated for every representation $(A,c)$ of $E_{\rm in}$ (resp. $E_{\rm out}$) with $\operatorname{Det}A\ne0$. The scaled set does not depend on the representation. Central symmetry means symmetry about some point. Volume is Lebesgue measure divided by the measure of the unit Euclidean ball. The book leaves the proof to Exercise 4.71. The degenerate case $n=0$, which the book does not consider, holds trivially.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 259, Theorem 4.9.1

import Mathlib
import Definitions.Def_ModernConvex_Ellipsoids_Ellipsoid

open Matrix

namespace ModernConvex.Ellipsoids

/-- Ben-Tal–Nemirovski, Theorem 4.9.1 (Löwner–Fritz John), p. 259. Let `S ⊂ ℝⁿ` be a solid. Then
(i) there exists and is uniquely defined the largest volume full-dimensional ellipsoid `E_in`
contained in `S`; the concentric to `E_in` `n` times larger ellipsoid contains `S`, and if `S` is
central-symmetric already the `√n` times larger one does;
(ii) there exists and is uniquely defined the smallest volume full-dimensional ellipsoid `E_out`
containing `S`; the concentric to `E_out` `n` times smaller ellipsoid is contained in `S`, and if
`S` is central-symmetric already the `√n` times smaller one is.
"Concentric, `r` times larger" ellipsoid of `E = {Au + c | uᵀu ≤ 1}` is `{(rA)u + c | uᵀu ≤ 1}`. -/
theorem lowner_fritz_john {n : ℕ} (S : Set (Fin n → ℝ)) (hS : IsSolid S) :
    ((∃! E : Set (Fin n → ℝ), IsMaxVolInscribed S E) ∧
      ∀ (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ), A.det ≠ 0 →
        IsMaxVolInscribed S (ellipsoid A c) →
          S ⊆ ellipsoid ((n : ℝ) • A) c ∧
            (IsCentralSymmetric S → S ⊆ ellipsoid (Real.sqrt n • A) c)) ∧
    ((∃! E : Set (Fin n → ℝ), IsMinVolCircumscribed S E) ∧
      ∀ (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ), A.det ≠ 0 →
        IsMinVolCircumscribed S (ellipsoid A c) →
          ellipsoid ((1 / (n : ℝ)) • A) c ⊆ S ∧
            (IsCentralSymmetric S → ellipsoid ((1 / Real.sqrt n) • A) c ⊆ S)) := by sorry

end ModernConvex.Ellipsoids
