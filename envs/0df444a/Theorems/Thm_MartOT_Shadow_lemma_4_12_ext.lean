-- Prove2me | Theorems.Thm_MartOT_Shadow_lemma_4_12_ext
-- name    : MartOT.Shadow.lemma_4_12_ext
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-05T05:00:03.508286+00:00
-- url     : https://prove2.me/theorems/fa2b7568-de68-490e-b966-fccf53548b69
-- title:
--   Lemma 4.12 (first assertion), p. 27 — for an atom δ with δ + γ ⪯_E ν, γ ⪯_E ν − S^ν(δ)
-- statement:
--   Let $\mathcal M$ be the finite Borel measures on $\mathbb R$ with finite first moment, and write $\mu\preceq_E\nu$ (extended convex order) if $\int\varphi\,d\mu\le\int\varphi\,d\nu$ for every nonnegative convex $\varphi:\mathbb R\to\mathbb R$. For $\mu\preceq_E\nu$, the shadow $S^\nu(\mu)$ is the measure $\eta\le\nu$ with $\mu\preceq_C\eta$ that is smallest in the convex order among all such measures (Lemma 4.6).
--
--   Let $\delta=\alpha\,\delta_x$ be an atom of mass $\alpha\ge0$ at $x\in\mathbb R$, and let $\gamma,\nu\in\mathcal M$ with $\delta+\gamma\preceq_E\nu$. Then
--   $$\gamma\preceq_E\nu-S^\nu(\delta).$$
--
--   This is the first assertion of Lemma 4.12: after the shadow of a single atom is removed from $\nu$, the rest of the measure still dominates $\gamma$ in the extended convex order, so the shadow $S^{\nu-S^\nu(\delta)}(\gamma)$ exists. It is the step that makes the decomposition $S^\nu(\delta+\gamma)=S^\nu(\delta)+S^{\nu-S^\nu(\delta)}(\gamma)$ of Lemma 4.12 meaningful.
--
--   **Formalization note.** The shadow is encoded by the predicate `IsShadow ν δ η1`, properties (i)–(iii) of Lemma 4.6, and the claim is stated for every such $\eta_1$. The difference $\nu-\eta_1$ is Mathlib's truncated subtraction of measures, which is the paper's difference because $\eta_1\le\nu$.
-- source:
--   Beiglböck–Juillet, On a problem of optimal transport under marginal martingale constraints, arXiv:1208.1509v2, Lemma 4.12 (first assertion: γ ⪯_E ν − S^ν(δ)), p. 27

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Shadow

open MeasureTheory NNReal

theorem lemma_4_12_ext (α : ℝ≥0) (x : ℝ) (γ ν : Measure ℝ) (hγ : MartOT.Var.InM γ)
    (hν : MartOT.Var.InM ν)
    (h : MartOT.Var.ExtConvexLE ((α : ENNReal) • Measure.dirac x + γ) ν) :
    ∀ η1 : Measure ℝ, MartOT.Var.IsShadow ν ((α : ENNReal) • Measure.dirac x) η1 →
      MartOT.Var.ExtConvexLE γ (ν - η1) := by sorry

end MartOT.Shadow
