-- Prove2me | Theorems.Thm_MartOT_Shadow_lemma_4_11
-- name    : MartOT.Shadow.lemma_4_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:46.983105+00:00
-- url     : https://prove2.me/theorems/bb0913dc-239d-4d3f-a066-6204bb7574b5
-- title:
--   Lemma 4.11, p. 27 — for an atom δ ⪯E η with η ≤ ν, η − S^η(δ) ≤ ν − S^ν(δ)
-- statement:
--   Let $\delta=\alpha\,\delta_x$ be an atom of mass $\alpha\ge0$ at a point $x\in\mathbb R$. Let $\eta\le\nu$ be finite Borel measures on $\mathbb R$, with $\nu$ of finite first moment, and assume $\delta\preceq_E\eta$ (extended convex order). Then
--   $$\eta-S^\eta(\delta)\le\nu-S^\nu(\delta),$$
--   where $S^\eta(\delta)$ and $S^\nu(\delta)$ are the shadows of $\delta$ in $\eta$ and in $\nu$.
--
--   Removing the shadow of an atom is monotone in the target measure; this comparison is the key step in the proof of Lemma 4.12.
--
--   **Formalization Note** The statement is quantified over all shadows of $\delta$ in $\eta$ and in $\nu$ (both exist and are unique by Lemma 4.6, since $\delta\preceq_E\eta\le\nu$). The paper's ambient assumption $\nu\in\mathcal M$ is written explicitly. Shadows are encoded as the predicate `IsShadow ν μ η` (properties (i)–(iii) of Lemma 4.6), never as a chosen function; by Lemma 4.6 a shadow exists and is unique under the stated hypotheses, so quantifying over all $\eta$ with `IsShadow` is equivalent to speaking of $S^\nu(\mu)$. The subtraction $\nu-\eta$ is Mathlib's truncated subtraction of measures; it is the paper's difference whenever $\eta\le\nu$, which is guaranteed here by property (i) of the shadow.
-- source:
--   arXiv:1208.1509v2, Lemma 4.11, p. 27

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Shadow

open MeasureTheory NNReal

theorem lemma_4_11 (α : ℝ≥0) (x : ℝ) (η ν : Measure ℝ) (hν : MartOT.Var.InM ν) (hην : η ≤ ν)
    (h : MartOT.Var.ExtConvexLE ((α : ENNReal) • Measure.dirac x) η) :
    ∀ ση σν : Measure ℝ, MartOT.Var.IsShadow η ((α : ENNReal) • Measure.dirac x) ση →
      MartOT.Var.IsShadow ν ((α : ENNReal) • Measure.dirac x) σν → η - ση ≤ ν - σν := by sorry

end MartOT.Shadow
