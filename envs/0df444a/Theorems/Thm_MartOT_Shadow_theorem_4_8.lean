-- Prove2me | Theorems.Thm_MartOT_Shadow_theorem_4_8
-- name    : MartOT.Shadow.theorem_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:20:24.361591+00:00
-- url     : https://prove2.me/theorems/a556b1f5-341c-4d5d-9893-a3b2a41f9983
-- title:
--   Theorem 4.8, p. 25 — shadow of a sum: S^ν(γ1 + γ2) = S^ν(γ1) + S^{ν−S^ν(γ1)}(γ2)
-- statement:
--   Let $\mathcal M$ be the finite Borel measures on $\mathbb R$ with finite first moment. For $\mu,\nu\in\mathcal M$ write $\mu\preceq_C\nu$ (convex order) if $\int\varphi\,d\mu\le\int\varphi\,d\nu$ for every convex $\varphi:\mathbb R\to\mathbb R$, and $\mu\preceq_E\nu$ (extended convex order) if this holds for every nonnegative convex $\varphi$. When $\mu\preceq_E\nu$, the **shadow** $S^\nu(\mu)$ of $\mu$ in $\nu$ is the unique measure $\eta$ with $\eta\le\nu$, $\mu\preceq_C\eta$, and $\eta\preceq_C\eta'$ for every $\eta'\le\nu$ with $\mu\preceq_C\eta'$.
--
--   Let $\gamma_1,\gamma_2,\nu\in\mathcal M$ and assume $\mu=\gamma_1+\gamma_2\preceq_E\nu$. Then
--   $$\gamma_2\preceq_E\nu-S^\nu(\gamma_1)$$
--   and
--   $$S^\nu(\gamma_1+\gamma_2)=S^\nu(\gamma_1)+S^{\nu-S^\nu(\gamma_1)}(\gamma_2).$$
--
--   Embedding $\gamma_1$ first and then $\gamma_2$ into what remains of $\nu$ gives the same result as embedding $\gamma_1+\gamma_2$ at once. Applied to $\gamma_1=\mu|_{]-\infty,x]}$, $\gamma_2=\mu|_{]x,x']}$, it is what makes the left-curtain coupling well defined.
--
--   **Formalization Note** The conclusion is stated for every shadow $\eta_1$ of $\gamma_1$ in $\nu$: $\gamma_2\preceq_E\nu-\eta_1$, and for every shadow $\eta_2$ of $\gamma_2$ in $\nu-\eta_1$, the measure $\eta_1+\eta_2$ is a shadow of $\gamma_1+\gamma_2$ in $\nu$. Since shadows exist and are unique under these hypotheses (Lemma 4.6), this is exactly the page's identity. Nothing in the hypotheses asserts $\eta_1+\eta_2\le\nu$ or $\gamma_1+\gamma_2\preceq_C\eta_1+\eta_2$: both are part of the conclusion. Shadows are encoded as the predicate `IsShadow ν μ η` (properties (i)–(iii) of Lemma 4.6), never as a chosen function; by Lemma 4.6 a shadow exists and is unique under the stated hypotheses, so quantifying over all $\eta$ with `IsShadow` is equivalent to speaking of $S^\nu(\mu)$. The subtraction $\nu-\eta$ is Mathlib's truncated subtraction of measures; it is the paper's difference whenever $\eta\le\nu$, which is guaranteed here by property (i) of the shadow.
-- source:
--   arXiv:1208.1509v2, Theorem 4.8, p. 25

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Shadow

open MeasureTheory

theorem theorem_4_8 (γ1 γ2 ν : Measure ℝ) (h1 : MartOT.Var.InM γ1) (h2 : MartOT.Var.InM γ2) (hν : MartOT.Var.InM ν)
    (h : MartOT.Var.ExtConvexLE (γ1 + γ2) ν) :
    ∀ η1 : Measure ℝ, MartOT.Var.IsShadow ν γ1 η1 →
      MartOT.Var.ExtConvexLE γ2 (ν - η1) ∧
      ∀ η2 : Measure ℝ, MartOT.Var.IsShadow (ν - η1) γ2 η2 → MartOT.Var.IsShadow ν (γ1 + γ2) (η1 + η2) := by sorry

end MartOT.Shadow
