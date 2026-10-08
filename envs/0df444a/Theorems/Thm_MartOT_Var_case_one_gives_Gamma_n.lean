-- Prove2me | Theorems.Thm_MartOT_Var_case_one_gives_Gamma_n
-- name    : MartOT.Var.case_one_gives_Gamma_n
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:10.348746+00:00
-- url     : https://prove2.me/theorems/a1f57292-c9cc-4c25-9a44-f2e5e38e3d81
-- title:
--   Proof of Lemma 1.11, p. 18 — in case (1) of Theorem 3.1, a Borel Γₙ of full π-measure supports no improvable α with |spt α| ≤ n
-- statement:
--   Let $c:\mathbb R\times\mathbb R\to\mathbb R$ be a cost, $\pi$ a measure on $\mathbb R^2$, $n\in\mathbb N$, and let $M\subseteq(\mathbb R^2)^n$ be the set of bad $n$-tuples (those carrying a finite measure that some competitor beats). Suppose case (1) of Theorem 3.1 holds: there are $M_1,\dots,M_n\subseteq(\mathbb R^2)^n$ with $\pi(\operatorname{proj}^i M_i)=0$ and $M\subseteq\bigcup_i M_i$. Put $N=\bigcup_{i=1}^n\operatorname{proj}^i(M_i)$.
--
--   Then there is a Borel set $\Gamma_n\subseteq\mathbb R^2\setminus N$ with $\pi(\mathbb R^2\setminus\Gamma_n)=0$ such that for every finite set $S\subseteq\Gamma_n$ with $|S|\le n$, every choice of weights $w_s\ge0$, the measure $\alpha=\sum_{s\in S}w_s\delta_s$ satisfies
--   $$\int c\,d\alpha\le\int c\,d\alpha'\qquad\text{for every competitor }\alpha'\text{ of }\alpha.$$
--
--   This is the half of the dichotomy that produces the set $\Gamma_n$ of the variational lemma.
--
--   **Formalization Note** The page sets $\Gamma_n:=\mathbb R^2\setminus N$; $N$ is $\pi$-null (in outer measure) but need not be Borel, and the lemma asks for a Borel $\Gamma$, so the statement asks for a Borel $\Gamma_n$ of full measure inside $\mathbb R^2\setminus N$. The hypotheses of the variational lemma on $c$ and $\pi$ are not needed for this step and are dropped, which makes the statement stronger. A finitely supported finite measure is written as a finite weighted sum of Dirac masses; zero weights are allowed and change nothing.
-- source:
--   arXiv:1208.1509v2, §3, proof of Lemma 1.11, p. 18 ("If we are in case (1), …")

import Mathlib
import Definitions.Def_MartOT_Var_BadTuples

namespace MartOT.Var

open MeasureTheory

theorem case_one_gives_Gamma_n (c : ℝ → ℝ → ℝ) (π : Measure (ℝ × ℝ)) (n : ℕ)
    (Ms : Fin n → Set (Fin n → ℝ × ℝ))
    (hnull : ∀ i, π ((fun z : Fin n → ℝ × ℝ => z i) '' Ms i) = 0)
    (hcover : BadTuples c n ⊆ ⋃ i, Ms i) :
    ∃ Γn : Set (ℝ × ℝ), MeasurableSet Γn ∧ π Γnᶜ = 0 ∧
      Γn ⊆ (⋃ i, (fun z : Fin n → ℝ × ℝ => z i) '' Ms i)ᶜ ∧
      ∀ (S : Finset (ℝ × ℝ)) (w : ℝ × ℝ → NNReal), S.card ≤ n →
        (↑S : Set (ℝ × ℝ)) ⊆ Γn → ∀ α' : Measure (ℝ × ℝ),
          IsCompetitor (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) α' →
          cost c (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) ≤ cost c α' := by sorry

end MartOT.Var
