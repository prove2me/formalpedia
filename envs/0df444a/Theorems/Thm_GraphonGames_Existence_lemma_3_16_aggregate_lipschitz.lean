-- Prove2me | Theorems.Thm_GraphonGames_Existence_lemma_3_16_aggregate_lipschitz
-- name    : GraphonGames.Existence.lemma_3_16_aggregate_lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:54:56.006685+00:00
-- url     : https://prove2.me/theorems/3383bcc0-41b7-40ae-80d4-b8d775059981
-- title:
--   Lemma 3.16, (15), p. 15 — ‖Zα¹ − Zα²‖ ≤ (√c_α‖W‖/(1 − √c_z‖W‖))‖α¹ − α²‖
-- statement:
--   Let $w$ be a graphon with operator $\mathbf W$, let $b,\mu_0$ satisfy Assumption 1 with constants $c_\alpha,c_z$, and assume $\sqrt{c_z}\|\mathbf W\|<1$. For profiles $\alpha^1,\alpha^2\in L^2(I)$ with aggregates $\mathbf Z\alpha^1,\mathbf Z\alpha^2$ (solutions of (6)),
--   $$\|\mathbf Z\alpha^1-\mathbf Z\alpha^2\|_{L^2(I)}\le\frac{\sqrt{c_\alpha}\,\|\mathbf W\|}{1-\sqrt{c_z}\,\|\mathbf W\|}\,\|\alpha^1-\alpha^2\|_{L^2(I)}.$$
--
--   This is the $L^2$ bound (15) of Lemma 3.16; it gives continuity of the aggregate map, which the existence proof uses.
--
--   **Formalization Note.** Only (15) is stated; the pointwise bound (16) of the same lemma is not. The statement is for any two aggregates, which by Proposition 3.1 are the aggregates.
-- source:
--   Carmona, Cooney, Graves & Laurière, Stochastic Graphon Games: I. The Static Case, arXiv:1911.10664v1, p. 15, Lemma 3.16, (15)

import Mathlib
import Definitions.Def_GraphonGames_Existence_Setting

open MeasureTheory
open scoped ENNReal

namespace GraphonGames.Existence

theorem lemma_3_16_aggregate_lipschitz (b : ℝ → ℝ → ℝ) (μ0 : Measure ℝ) (cα cz : ℝ)
    (h1 : Asm1 b μ0 cα cz) (w : I → I → ℝ) (hw : IsGraphon w)
    (hW : Real.sqrt cz * (opNorm w).toReal < 1)
    (α1 α2 : I → ℝ) (hα1 : MemLp α1 2 volume) (hα2 : MemLp α2 2 volume)
    (z1 z2 : I → ℝ) (hz1 : IsAggregate w b α1 z1) (hz2 : IsAggregate w b α2 z2) :
    eLpNorm (z1 - z2) 2 volume ≤
      ENNReal.ofReal (Real.sqrt cα * (opNorm w).toReal / (1 - Real.sqrt cz * (opNorm w).toReal)) *
        eLpNorm (α1 - α2) 2 volume := by sorry

end GraphonGames.Existence
