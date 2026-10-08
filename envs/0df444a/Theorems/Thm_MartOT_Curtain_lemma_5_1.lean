-- Prove2me | Theorems.Thm_MartOT_Curtain_lemma_5_1
-- name    : MartOT.Curtain.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:20:23.425199+00:00
-- url     : https://prove2.me/theorems/e3579fd8-e9ad-49ae-9cc1-4fcf9157d2a6
-- title:
--   Lemma 5.1, p. 33 — for µ ⪯C ν, the three possible configurations at the right (and left) end of spt µ
-- statement:
--   Let $\mu,\nu$ be finite Borel measures on $\mathbb R$ with finite first moment, and $\mu\preceq_C\nu$. Write $\operatorname{spt}\mu$ for the closed support of $\mu$. Then one of the following holds:
--
--   1. $\mu(]a,+\infty[)>0$ and $\nu(]a,+\infty[)>0$ for every $a\in\mathbb R$;
--   2. $\operatorname{spt}\mu$ is bounded above, and with $a=\sup\operatorname{spt}\mu$ we have $\nu(]a,+\infty[)>0$;
--   3. $\operatorname{spt}\mu$ is bounded above, and with $a=\sup\operatorname{spt}\mu$ we have $\nu(]a,+\infty[)=0$ and $\nu(\{a\})\ge\mu(\{a\})$.
--
--   The corresponding statement holds at the left end: either $\mu(]-\infty,b[)>0$ and $\nu(]-\infty,b[)>0$ for every $b$; or $b=\inf\operatorname{spt}\mu$ is finite and $\nu(]-\infty,b[)>0$; or $b=\inf\operatorname{spt}\mu$ is finite, $\nu(]-\infty,b[)=0$ and $\nu(\{b\})\ge\mu(\{b\})$.
--
--   In words: if $\nu$ puts no mass beyond the last point of the support of $\mu$, then it carries at least as much mass at that point as $\mu$ does. The uniqueness proof of the left-curtain coupling applies it to sub-probability pieces of the two couplings being compared.
--
--   **Formalization Note** The support is Mathlib's `Measure.support` (points all of whose neighbourhoods have positive mass); "finite" is `BddAbove` / `BddBelow` of the support, and then $a$ is its real supremum (infimum). For $\mu=0$ (which forces $\nu=0$) the page's "number $\sup(\operatorname{spt}\mu)$" does not exist; Lean's convention $\sup\emptyset=0$ makes the third alternative hold trivially there, so no hypothesis $\mu\neq0$ is needed. The two halves are the two conjuncts; "one of the following" is an inclusive "or".
-- source:
--   arXiv:1208.1509v2, Lemma 5.1, p. 33

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Curtain

open MeasureTheory

theorem lemma_5_1 (μ ν : Measure ℝ) (hμν : MartOT.Var.ConvexLE μ ν) :
    ((∀ a : ℝ, 0 < μ (Set.Ioi a) ∧ 0 < ν (Set.Ioi a)) ∨
      (BddAbove μ.support ∧ 0 < ν (Set.Ioi (sSup μ.support))) ∨
      (BddAbove μ.support ∧ ν (Set.Ioi (sSup μ.support)) = 0 ∧
        μ {sSup μ.support} ≤ ν {sSup μ.support})) ∧
    ((∀ b : ℝ, 0 < μ (Set.Iio b) ∧ 0 < ν (Set.Iio b)) ∨
      (BddBelow μ.support ∧ 0 < ν (Set.Iio (sInf μ.support))) ∨
      (BddBelow μ.support ∧ ν (Set.Iio (sInf μ.support)) = 0 ∧
        μ {sInf μ.support} ≤ ν {sInf μ.support})) := by sorry

end MartOT.Curtain
