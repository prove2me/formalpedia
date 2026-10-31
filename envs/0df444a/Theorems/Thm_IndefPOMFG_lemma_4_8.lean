-- Prove2me | Theorems.Thm_IndefPOMFG_lemma_4_8
-- name    : IndefPOMFG.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:13:59.264354+00:00
-- url     : https://prove2.me/theorems/5c059c03-856b-479e-8b13-a519275c889f
-- title:
--   Lemma 4.8 — Schur's complement
-- statement:
--   Let $Q\in\mathbb S^n$, $R\in\mathbb S^m$ and $S\in\mathbb R^{n\times m}$. The following are equivalent:
--
--   1. $R\gg0$ and $Q-SR^{-1}S^\top\ge0$;
--   2. $R\gg0$ and $\begin{pmatrix}Q&S\\S^\top&R\end{pmatrix}\ge0$.
--
--   The paper cites it from Albert (1969, Theorem 1) and uses it to rewrite Condition (PD) for the compensated weights as Condition (RC).
--
--   Differences from the source:
--   - encoding: R ≫ 0 and "≥ 0" for constant symmetric matrices (Lemma 4.8) → Matrix.PosDef and Matrix.PosSemidef; reason: for a constant matrix, uniform positive definiteness is positive definiteness
-- source:
--   Chen, Nie & Wu, Indefinite Linear-Quadratic Partially Observed Mean-Field Game, arXiv:2508.01568v1, Lemma 4.8, p.11 (citing [1, Theorem 1])

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_IndefPOMFG_Coeffs
import Definitions.Def_IndefPOMFG_Space
import Definitions.Def_IndefPOMFG_NPlayer
import Definitions.Def_IndefPOMFG_Limiting

open MeasureTheory Set Peng1990.SMP
open scoped NNReal ENNReal Matrix

namespace IndefPOMFG

/-- Lemma 4.8 (Schur's complement; Chen–Nie–Wu, arXiv:2508.01568v1, p.11, citing [1, Theorem 1]):
let `Q ∈ 𝕊ⁿ`, `R ∈ 𝕊ᵐ` and `S ∈ ℝ^{n×m}`. Then `R ≫ 0` and `Q − SR⁻¹Sᵀ ≥ 0` if and only if `R ≫ 0` and
`[Q S; Sᵀ R] ≥ 0`.

**Formalization Note** For a constant matrix, `R ≫ 0` is positive definiteness (`Matrix.PosDef`);
`≥ 0` is `Matrix.PosSemidef`. -/
theorem lemma_4_8 {n m : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (S : Matrix (Fin n) (Fin m) ℝ) (hQ : Q.IsSymm) (hR : R.IsSymm) :
    (R.PosDef ∧ (Q - S * R⁻¹ * Sᵀ).PosSemidef) ↔
      (R.PosDef ∧ (Matrix.fromBlocks Q S Sᵀ R).PosSemidef) := by sorry

end IndefPOMFG
