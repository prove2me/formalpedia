-- Prove2me | Theorems.Thm_MartOT_Curtain_curtain_measure_exists
-- name    : MartOT.Curtain.curtain_measure_exists
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-05T05:26:39.872045+00:00
-- url     : https://prove2.me/theorems/6861a988-9f7a-41ea-9156-154ee1e9ba36
-- title:
--   Proof of Theorem 4.18, p. 31 — an increasing family $S_x$ with $S_x(\mathbb R)=\mu(]-\infty,x])$ defines a plan with $\pi(]-\infty,x]\times A)=S_x(A)$
-- statement:
--   Let $\mu$ be a finite Borel measure on $\mathbb R$ and let $(S_x)_{x\in\mathbb R}$ be a family of finite Borel measures on $\mathbb R$ that is **increasing**, i.e. $S_x\le S_{x'}$ setwise whenever $x\le x'$, and whose masses are $S_x(\mathbb R)=\mu(]-\infty,x])$ for every $x$. Then there is a finite measure $\pi$ on $\mathbb R\times\mathbb R$ such that, for every $x\in\mathbb R$,
--
--   $$\mathrm{proj}^x_\#\big(\pi|_{]-\infty,x]\times\mathbb R}\big)=\mu|_{]-\infty,x]}\qquad\text{and}\qquad \mathrm{proj}^y_\#\big(\pi|_{]-\infty,x]\times\mathbb R}\big)=S_x ,$$
--
--   that is, $\pi(]-\infty,x]\times A)=S_x(A)$ for all Borel $A$ (the second condition is written with `MartOT.Var.targetUpTo π x`, the paper's $\nu^\pi_x$).
--
--   This is the measure-construction step of the proof of Theorem 4.18 in Beiglböck–Juillet: "the condition given in the statement prescribes the value of $\pi_{lc}(]-\infty,x]\times A)=S^\nu(\mu|_{]-\infty,x]})(A)$ for $x\in\mathbb R$ and every Borel set $A$, thus giving rise to a unique measure on the product space. Here we use that, by Theorem 4.8, $S^\nu(\mu|_{]-\infty,x]})\le S^\nu(\mu|_{]-\infty,x']})$ whenever $x\le x'$." Here it is stated for an abstract increasing family. The mass condition gives that $x\mapsto S_x(A)$ is right-continuous and vanishes at $-\infty$: for $x<x'$ we have $S_{x'}(A)-S_x(A)\le\mu(]x,x'])$. So each $x\mapsto S_x(A)$ is the distribution function of a measure $m_A\le\mu$ on the $x$-axis, and $\pi$ is obtained by disintegrating against $\mu$ (for instance $\pi=\mu\otimes\kappa$ with a kernel $\kappa$ built from the densities $dm_{]-\infty,r]}/d\mu$, $r\in\mathbb Q$).
-- source:
--   arXiv:1208.1509v2 (Beiglböck–Juillet, On a problem of optimal transport under marginal martingale constraints), proof of Theorem 4.18, p. 31 (construction of π_lc from the increasing family of shadows)

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Curtain

open MeasureTheory

theorem curtain_measure_exists (μ : Measure ℝ) [IsFiniteMeasure μ] (S : ℝ → Measure ℝ)
    (hfin : ∀ x, IsFiniteMeasure (S x)) (hmono : ∀ x x', x ≤ x' → S x ≤ S x')
    (hmass : ∀ x, S x Set.univ = μ (Set.Iic x)) :
    ∃ π : Measure (ℝ × ℝ), IsFiniteMeasure π ∧
      ∀ x : ℝ, (π.restrict (Set.Iic x ×ˢ Set.univ)).map Prod.fst = μ.restrict (Set.Iic x) ∧
        MartOT.Var.targetUpTo π x = S x := by sorry

end MartOT.Curtain
