-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_memW_of_isTestFunction
-- name    : HunterPDE.Sobolev.memW_of_isTestFunction
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-10T22:34:19.431233+00:00
-- url     : https://prove2.me/theorems/3bcd6ef6-9b41-4070-b1c0-92e86cdffb55
-- title:
--   Sobolev membership of smooth compactly supported functions
-- statement:
--   For every nonnegative integer $k$, every $1\le p\le\infty$, and every smooth compactly supported real function $\varphi$ on $\mathbb R^n$,
--
--   $$\varphi\in W^{k,p}(\mathbb R^n).$$
--
--   This supplies Sobolev membership of test functions for density and embedding arguments. The order-zero and dimension-zero cases are included.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, Definitions 3.1–3.2 (printed pp. 47–48), Definition 3.23 (p. 58), and the test-function approximants in the proof of Theorem 3.24 (p. 59). Sobolev membership follows by repeated integration by parts and compact support of the classical derivatives.

import Definitions.Def_HunterPDE_Sobolev_SobolevSpace

open MeasureTheory HunterPDE.Sobolev

theorem HunterPDE.Sobolev.memW_of_isTestFunction {n k : ℕ} {p : ENNReal}
    (hp : 1 ≤ p) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hφ : IsTestFunction Set.univ φ) : MemW k p Set.univ φ := by sorry
