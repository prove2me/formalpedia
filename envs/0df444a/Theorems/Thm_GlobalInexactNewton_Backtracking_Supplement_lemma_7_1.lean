-- Prove2me | Theorems.Thm_GlobalInexactNewton_Backtracking_Supplement_lemma_7_1
-- name    : GlobalInexactNewton.Backtracking.Supplement.lemma_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T08:52:46.539806+00:00
-- url     : https://prove2.me/theorems/dfe92923-01e4-4877-8bb8-96f20ef54231
-- title:
--   Lemma 7.1 — A strict reduction of the residual model gives a strict descent direction for ½‖F‖².
-- statement:
--   Let $F$ be continuously differentiable on a finite-dimensional real inner product space. At any $x$, if a step $s$ strictly reduces the local residual model, $\|F(x)+F'(x)s\|<\|F(x)\|$, then
--
--   $$\langle F'(x)^*F(x),s\rangle<0.$$
--
--   Thus $s$ is a strict descent direction for $f(x)=\tfrac12\|F(x)\|^2$. This is the sign needed in the equality-curve angle estimate.
--
--   **Formalization Note** The paper states its results on $\mathbb R^n$; we use a finite-dimensional real space with exactly its specified norm and `ContDiff ℝ 1 F`. All curve restrictions refer only to their stated level intervals.
--
--   Differences from the source:
--   - encoding: Real n-dimensional vectors, continuously differentiable F, and the paper’s algorithm or local data. → Finite-dimensional real normed spaces (inner product spaces in §§7–8), fderiv with ContDiff ℝ 1, and explicit data predicates.; reason: These are coordinate-independent representations with exactly the stated norm; a run on infinite sequences means no breakdown.
-- source:
--   Eisenstat and Walker, Globally Convergent Inexact Newton Methods, SIAM J. Optim. 4(2) (1994), p. 413, Lemma 7.1; DOI 10.1137/0804022

import Mathlib
import Definitions.Def_GlobalInexactNewton_Backtracking_Method
import Definitions.Def_GlobalInexactNewton_Backtracking_Supplement_EqualityCurves

namespace GlobalInexactNewton.Backtracking.Supplement

open Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem lemma_7_1 (F : E → E) (hF : ContDiff ℝ 1 F) (x s : E)
    (h : ‖F x + fderiv ℝ F x s‖ < ‖F x‖) :
    inner ℝ ((fderiv ℝ F x).adjoint (F x)) s < 0 := by sorry

end GlobalInexactNewton.Backtracking.Supplement
