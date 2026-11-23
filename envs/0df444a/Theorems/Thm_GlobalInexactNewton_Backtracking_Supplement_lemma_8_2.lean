-- Prove2me | Theorems.Thm_GlobalInexactNewton_Backtracking_Supplement_lemma_8_2
-- name    : GlobalInexactNewton.Backtracking.Supplement.lemma_8_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T08:59:58.87434+00:00
-- url     : https://prove2.me/theorems/f615420c-a4bc-43f8-98da-d793b7215e63
-- title:
--   Lemma 8.2 — Inexact Newton residual bound implies the explicit angle bound (1 − η)/(1 + η).
-- statement:
--   At a point $x$ with $\|F(x)\|\ne0$, suppose $\eta\in[0,1)$ and $\|F(x)+F'(x)s\|\le\eta\|F(x)\|$. Then
--
--   $$\frac{|\langle F(x),F'(x)s\rangle|}{\|F(x)\|\|F'(x)s\|}\ge\frac{1-\eta}{1+\eta}.$$
--
--   The strict upper bound on $\eta$ ensures $F'(x)s\ne0$. The estimate controls the angle of the first residual-minimizing segment.
--
--   **Formalization Note** The paper states its results on $\mathbb R^n$; we use a finite-dimensional real space with exactly its specified norm and `ContDiff ℝ 1 F`. All curve restrictions refer only to their stated level intervals.
--
--   Differences from the source:
--   - encoding: Real n-dimensional vectors, continuously differentiable F, and the paper’s algorithm or local data. → Finite-dimensional real normed spaces (inner product spaces in §§7–8), fderiv with ContDiff ℝ 1, and explicit data predicates.; reason: These are coordinate-independent representations with exactly the stated norm; a run on infinite sequences means no breakdown.
-- source:
--   Eisenstat and Walker, Globally Convergent Inexact Newton Methods, SIAM J. Optim. 4(2) (1994), p. 416, Lemma 8.2; DOI 10.1137/0804022

import Mathlib
import Definitions.Def_GlobalInexactNewton_Backtracking_Method
import Definitions.Def_GlobalInexactNewton_Backtracking_Supplement_EqualityCurves

namespace GlobalInexactNewton.Backtracking.Supplement

open Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem lemma_8_2 (F : E → E) (hF : ContDiff ℝ 1 F) (x s : E)
    (η : ℝ) (hη : η ∈ Set.Ico (0 : ℝ) 1) (hFx : ‖F x‖ ≠ 0)
    (hstep : InexactNewtonCond F x s η) :
    (1 - η) / (1 + η) ≤ residualAngle F x s := by sorry

end GlobalInexactNewton.Backtracking.Supplement
