-- Prove2me | Theorems.Thm_MartOT_Curtain_lemma_4_6
-- name    : MartOT.Curtain.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:17.034866+00:00
-- url     : https://prove2.me/theorems/10502042-8ea7-4b76-90de-a0892ba5a12c
-- title:
--   Lemma 4.6, p. 23 — shadow embedding: for µ ⪯E ν in 𝓜 the shadow S^ν(µ) exists, is unique, and satisfies (iii′)
-- statement:
--   Let $\mu,\nu$ be finite Borel measures on $\mathbb R$ with finite first moment, and assume $\mu\preceq_E\nu$ (extended convex order: $\int\varphi\,d\mu\le\int\varphi\,d\nu$ for every nonnegative convex $\varphi$). Call $\eta$ a **shadow of $\mu$ in $\nu$** if
--
--   1. $\eta\le\nu$;
--   2. $\mu\preceq_C\eta$;
--   3. $\eta\preceq_C\eta'$ for every measure $\eta'$ satisfying 1 and 2.
--
--   Then there is exactly one shadow, denoted $S^\nu(\mu)$, and it moreover satisfies
--
--   $$\eta'\le\nu\ \text{ and }\ \mu\preceq_E\eta'\quad\Longrightarrow\quad S^\nu(\mu)\preceq_E\eta'. \tag{iii$'$}$$
--
--   The shadow is the "least spread out" part of $\nu$ into which $\mu$ can be embedded by a martingale; it is the building block of the left-curtain coupling, which transports each initial segment $\mu|_{]-\infty,x]}$ onto its shadow in $\nu$.
--
--   **Formalization Note** Shadows are encoded by the predicate of properties (i)–(iii) (`IsShadow ν μ η`), not by a function, so existence and uniqueness are the content of this statement: `∃!`. Uniqueness is meant among all measures on $\mathbb R$; conditions (ii)–(iii) force membership in $\mathcal M$.
-- source:
--   arXiv:1208.1509v2, Lemma 4.6, p. 23

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Curtain

open MeasureTheory

theorem lemma_4_6 (μ ν : Measure ℝ) (hμν : MartOT.Var.ExtConvexLE μ ν) :
    (∃! η : Measure ℝ, MartOT.Var.IsShadow ν μ η) ∧
      ∀ η : Measure ℝ, MartOT.Var.IsShadow ν μ η →
        ∀ η' : Measure ℝ, η' ≤ ν → MartOT.Var.ExtConvexLE μ η' → MartOT.Var.ExtConvexLE η η' := by sorry

end MartOT.Curtain
