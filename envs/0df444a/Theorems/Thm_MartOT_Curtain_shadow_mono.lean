-- Prove2me | Theorems.Thm_MartOT_Curtain_shadow_mono
-- name    : MartOT.Curtain.shadow_mono
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:20:17.258858+00:00
-- url     : https://prove2.me/theorems/850bb466-cf92-4d19-b0fb-de8ca4d7e754
-- title:
--   §4.4, p. 31 — shadows are monotone: µ ≤ µ′ ⪯E ν implies S^ν(µ) ≤ S^ν(µ′)
-- statement:
--   Let $\mu,\mu',\nu$ be measures on $\mathbb R$ with $\mu\le\mu'$ (setwise) and $\mu'\preceq_E\nu$ in the extended convex order (in particular $\mu'$ and $\nu$ are finite with finite first moment). Then the shadows of $\mu$ and $\mu'$ in $\nu$ are ordered setwise:
--
--   $$S^\nu(\mu)\le S^\nu(\mu').$$
--
--   The paper derives this from Theorem 4.8 (shadow of a sum) and calls it "essential for the definition of $\pi_{\mathrm{lc}}$": it makes $x\mapsto S^\nu(\mu|_{]-\infty,x]})$ an increasing family of measures, which is what allows these shadows to be the images of the initial segments under a single transport plan.
--
--   **Formalization Note** Since shadows are a predicate (`IsShadow`), the claim reads: for every shadow $\eta$ of $\mu$ and every shadow $\eta'$ of $\mu'$ in $\nu$, $\eta\le\eta'$. Existence is Lemma 4.6. The hypothesis $\mu\in\mathcal M$ is not stated separately: it follows from $\mu\le\mu'\in\mathcal M$.
-- source:
--   arXiv:1208.1509v2, §4.4, p. 31 (paragraph before Theorem 4.18, consequence of Theorem 4.8)

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Curtain

open MeasureTheory

theorem shadow_mono (μ μ' ν : Measure ℝ) (hle : μ ≤ μ') (h : MartOT.Var.ExtConvexLE μ' ν) :
    ∀ η η' : Measure ℝ, MartOT.Var.IsShadow ν μ η → MartOT.Var.IsShadow ν μ' η' → η ≤ η' := by sorry

end MartOT.Curtain
