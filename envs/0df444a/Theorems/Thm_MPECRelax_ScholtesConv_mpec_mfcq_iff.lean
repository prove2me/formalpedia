-- Prove2me | Theorems.Thm_MPECRelax_ScholtesConv_mpec_mfcq_iff
-- name    : MPECRelax.ScholtesConv.mpec_mfcq_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:47:39.137253+00:00
-- url     : https://prove2.me/theorems/d7d846e0-b424-431f-9220-5bd9f158bf6b
-- title:
--   §2.2, pp. 6–7 — MPEC-MFCQ written out explicitly
-- statement:
--   Let $x^*$ be feasible for the MPEC (1), with index sets $I_g$, $I_{0+}$, $I_{00}$, $I_{+0}$ at $x^*$. Then MPEC-MFCQ (standard MFCQ for TNLP$(x^*)$, Definition 2.4) holds at $x^*$ if and only if the gradients
--
--   $$\nabla h_i(x^*)\ (i=1,\dots,p),\qquad\nabla G_i(x^*)\ (i\in I_{00}\cup I_{0+}),\qquad\nabla H_i(x^*)\ (i\in I_{00}\cup I_{+0})$$
--
--   are linearly independent, and there exists $d\in\mathbb R^n$ with
--   $$\langle\nabla g_i(x^*),d\rangle<0\ (i\in I_g),\quad\langle\nabla h_i(x^*),d\rangle=0\ (i=1,\dots,p),\quad\langle\nabla G_i(x^*),d\rangle=0\ (i\in I_{00}\cup I_{0+}),\quad\langle\nabla H_i(x^*),d\rangle=0\ (i\in I_{00}\cup I_{+0}).$$
--
--   This explicit form is the one the paper works with.
--
--   **Formalization Note** The gradients form one family indexed by the disjoint union $\{1,\dots,p\}\sqcup(I_{00}\cup I_{0+})\sqcup(I_{00}\cup I_{+0})$, so an index $i\in I_{00}$ contributes both $\nabla G_i(x^*)$ and $\nabla H_i(x^*)$, and repeated vectors count as dependent.
-- source:
--   Hoheisel, Kanzow, Schwartz, Theoretical and numerical comparison of relaxation methods for mathematical programs with complementarity constraints, Preprint 299, Univ. Würzburg, Sept. 2010, pp. 6–7, §2.2, explicit form of MPEC-MFCQ (unnumbered display after Definition 2.4)

import Mathlib
import Definitions.Def_MPECRelax_ScholtesConv_NLP
import Definitions.Def_MPECRelax_ScholtesConv_MPEC

open scoped RealInnerProductSpace

namespace MPECRelax.ScholtesConv

theorem mpec_mfcq_iff {n m p l : ℕ} (P : MPEC n m p l) (xs : E n) (hxs : P.Feasible xs) :
    P.MPEC_MFCQ xs ↔
      (LinearIndependent ℝ
          (Sum.elim (fun i : Fin p => gradient (P.h i) xs)
            (Sum.elim (fun i : ↥(P.I00 xs ∪ P.I0p xs) => gradient (P.G i) xs)
              (fun i : ↥(P.I00 xs ∪ P.Ip0 xs) => gradient (P.H i) xs))) ∧
        ∃ d : E n, (∀ i ∈ P.Ig xs, ⟪gradient (P.g i) xs, d⟫ < 0) ∧
          (∀ i, ⟪gradient (P.h i) xs, d⟫ = 0) ∧
          (∀ i ∈ P.I00 xs ∪ P.I0p xs, ⟪gradient (P.G i) xs, d⟫ = 0) ∧
          (∀ i ∈ P.I00 xs ∪ P.Ip0 xs, ⟪gradient (P.H i) xs, d⟫ = 0)) := by sorry

end MPECRelax.ScholtesConv
