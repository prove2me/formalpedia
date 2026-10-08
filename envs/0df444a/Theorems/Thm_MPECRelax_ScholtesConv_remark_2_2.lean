-- Prove2me | Theorems.Thm_MPECRelax_ScholtesConv_remark_2_2
-- name    : MPECRelax.ScholtesConv.remark_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:46:48.041585+00:00
-- url     : https://prove2.me/theorems/84920a73-2b81-4a0e-802c-617d740b172d
-- title:
--   Remark 2.2 — MFCQ iff the active inequality and all equality gradients are positive-linearly independent
-- statement:
--   Let $x^*$ be a feasible point of a nonlinear program (2) with finitely many inequality constraints $g_i\le0$ and equality constraints $h_j=0$, and let $I_g=\{i\mid g_i(x^*)=0\}$ be its active set. Then
--
--   $$x^*\ \text{satisfies MFCQ}\iff\{\nabla g_i(x^*)\mid i\in I_g\}\cup\{\nabla h_j(x^*)\mid j=1,\dots,p\}\ \text{is positive-linearly independent.}$$
--
--   This dual characterisation of MFCQ is the form used throughout the convergence analysis of relaxation methods: MPEC-MFCQ is applied as positive-linear independence of a family of gradients.
--
--   **Formalization Note** The statement concerns only the gradient values at $x^*$; no differentiability is assumed (for non-differentiable data, Mathlib's `gradient` is $0$, and the equivalence is still a statement about those vectors). Positive-linear independence is the negation of positive-linear dependence (Definition 2.1) with $I_1=I_g$ and $I_2$ all equality indices.
-- source:
--   Hoheisel, Kanzow, Schwartz, Theoretical and numerical comparison of relaxation methods for mathematical programs with complementarity constraints, Preprint 299, Univ. Würzburg, Sept. 2010, p. 4, Remark 2.2

import Mathlib
import Definitions.Def_MPECRelax_ScholtesConv_NLP

namespace MPECRelax.ScholtesConv

theorem remark_2_2 {n : ℕ} {ι κ : Type} [Fintype ι] [Fintype κ] (P : NLP n ι κ) (x : E n)
    (hx : P.Feasible x) :
    P.IsMFCQ x ↔ ¬ P.PosLinDep x (P.activeSet x) Set.univ := by sorry

end MPECRelax.ScholtesConv
