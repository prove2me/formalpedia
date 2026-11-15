-- Prove2me | Theorems.Thm_GibbsTransition_SizeCopies_Supplement_finite_size_order_parameter
-- name    : GibbsTransition.SizeCopies.Supplement.finite_size_order_parameter
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:43:09.166802+00:00
-- url     : https://prove2.me/theorems/a4c578ab-92be-4c25-b4b5-5a498ba92ce3
-- title:
--   Theorem A.1 — Finite-size order-parameter bound
-- statement:
--   For the full field-coupled class at any finite public dimension $q\ge1$, put $C=\max(1,3J+J_b)$. For every instance $u$, integer side $L\ge1$, real margin $\gamma>0$ and real field $\phi\in[0,1]$, the normalized whole-ground-space order parameter satisfies
--   $$\phi\le\theta_u-\gamma\ \Longrightarrow\ m_{u,L}(\phi)\in[0,a+4C/(L\gamma)],$$
--   $$\phi\ge\theta_u+\gamma\ \Longrightarrow\ m_{u,L}(\phi)\in[b-4C/(L\gamma),1].$$
--   Both closed-side endpoints are included. No phase promise at the transition itself, energy convergence hypothesis or nondegeneracy of the ground eigenspace is added.
--
--   The explicit finite-size estimate supplies the comparison gap for the Appendix A learner.
--
--   Differences from the source:
--   - encoding: general C_field and its normalized ground-space order parameter → arbitrary finite dimension on zero-based cube coordinates and the explicit full spectral projector; reason: coordinate translation is bijective and normalization includes every degenerate ground vector
--   - generalization: a boundary prescription with a uniform effective algebraic encoding → an algebraic Hermitian boundary prescription with a uniform computable rational Cauchy table; reason: an effective algebraic encoding supplies this table; the statements use only certified approximations and the same surface norm bound, so every source boundary is included without requiring uniform recovery of exact algebraic descriptions
-- source:
--   Yuhao Cai, Zhenzhang Li, STOC 2027 submission #1168 (October 2026), Theorem A.1, printed p. 22 (PDF p. 24); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1168.pdf

import Mathlib
import Definitions.Def_GibbsTransition_SizeCopies_Supplement_Field
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
set_option autoImplicit false

namespace GibbsTransition.SizeCopies.Supplement

theorem finite_size_order_parameter {q : ℕ} (p : FieldData q)
    (hp : ValidField p) (u : FieldInteraction q) (hu : InFieldClass p u)
    (L : ℕ) (hL : 1 ≤ L) (gamma : ℝ) (hg : 0 < gamma)
    (phi : ℝ) (hf : phi ∈ Set.Icc (0 : ℝ) 1) :
    (phi ≤ fieldTheta p u-gamma →
      fieldOrder p u L phi ∈ Set.Icc 0 ((p.a : ℝ)+4*(surfaceC p : ℝ)/((L : ℝ)*gamma))) ∧
    (fieldTheta p u+gamma ≤ phi →
      fieldOrder p u L phi ∈ Set.Icc ((p.b : ℝ)-4*(surfaceC p : ℝ)/((L : ℝ)*gamma)) 1) := by sorry

end GibbsTransition.SizeCopies.Supplement
