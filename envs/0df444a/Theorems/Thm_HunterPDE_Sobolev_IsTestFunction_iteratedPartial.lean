-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_IsTestFunction_iteratedPartial
-- name    : HunterPDE.Sobolev.IsTestFunction.iteratedPartial
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T23:00:58.432572+00:00
-- url     : https://prove2.me/theorems/d0b2d7d4-7353-464f-aad3-e4a9c78d4837
-- title:
--   Multi-index differentiation preserves test functions
-- statement:
--   Let $\Omega\subseteq\mathbb R^n$, and let $\varphi:\mathbb R^n\to\mathbb R$ be smooth with compact topological support contained in $\Omega$. For every multi-index $\alpha\in\mathbb N_0^n$,
--
--   $$D^\alpha\varphi\text{ is smooth, and }
--   \operatorname{supp}(D^\alpha\varphi)\text{ is compact and contained in }\Omega.$$
--
--   Thus differentiation preserves test functions and their support constraint. No openness assumption on $\Omega$ is needed; order zero and dimension zero are included.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, Section 1.8 (p. 10), Definitions 3.1–3.2 (pp. 47–48). Supporting calculus result: repeated integration by parts and support locality of derivatives.

import Definitions.Def_HunterPDE_Sobolev_SobolevSpace
open HunterPDE.Sobolev

theorem HunterPDE.Sobolev.IsTestFunction.iteratedPartial {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : IsTestFunction Ω φ)
    (α : Fin n → ℕ) : IsTestFunction Ω (iteratedPartial α φ) := by sorry
