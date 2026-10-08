-- Prove2me | Theorems.Thm_MPECRelax_ScholtesMFCQ_remark_2_2
-- name    : MPECRelax.ScholtesMFCQ.remark_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:09.244723+00:00
-- url     : https://prove2.me/theorems/c20fc68d-0f68-4262-9ed9-8db67714c9f8
-- title:
--   Remark 2.2 — MFCQ iff positive-linear independence of the active inequality and all equality gradients
-- statement:
--   Let $x^*$ be feasible for a nonlinear program (2) with finitely many inequality constraints $g_i\le 0$ and equality constraints $h_j=0$, and let $I_g=\{i\mid g_i(x^*)=0\}$ be the active set. Then $x^*$ satisfies MFCQ if and only if the family of vectors
--   $$\{\nabla g_i(x^*)\mid i\in I_g\}\cup\{\nabla h_j(x^*)\mid j=1,\dots,p\}$$
--   is positive-linearly independent in the sense of Definition 2.1 (sign constraint on the coefficients of the $\nabla g_i$ only).
--
--   This dual characterization of MFCQ is the form in which MFCQ is verified in the proof of Theorem 3.2: one shows that a vanishing nonnegative-on-inequalities combination of the active gradients is trivial.
--
--   **Formalization Note.** No differentiability hypothesis is needed: the statement is about the vectors `gradient (g i) x`, whatever they are. Families are indexed, so a repeated equality gradient makes both sides fail.
-- source:
--   Hoheisel, Kanzow, Schwartz, Theoretical and numerical comparison of relaxation methods for mathematical programs with complementarity constraints, Preprint 299, Univ. Würzburg, Sept. 2010, p. 4, Remark 2.2

import Mathlib
import Definitions.Def_MPECRelax_ScholtesMFCQ_Basic

open Filter Topology
open scoped RealInnerProductSpace

namespace MPECRelax.ScholtesMFCQ

/-- Remark 2.2 (p. 4): a point feasible for the NLP (2) satisfies MFCQ iff the family
`{∇g_i(x) | i ∈ I_g} ∪ {∇h_j(x) | j = 1, …, p}` is positive-linearly independent. -/
theorem remark_2_2 {n : ℕ} {ι κ : Type} [Fintype ι] [Fintype κ] (P : MPECRelax.ScholtesConv.NLP n ι κ) (x : MPECRelax.ScholtesConv.E n)
    (hx : P.Feasible x) :
    P.IsMFCQ x ↔ ¬ P.PosLinDep x (P.activeSet x) Set.univ := by sorry

end MPECRelax.ScholtesMFCQ
