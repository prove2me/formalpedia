-- Prove2me | Theorems.Thm_GraphAlignment_Impossible_theorem_3_1
-- name    : GraphAlignment.Impossible.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:31:12.942379+00:00
-- url     : https://prove2.me/theorems/fc9d3c06-f453-44e4-938c-d72ef55a195f
-- title:
--   Theorem 3.1, pp. 10–11 — generalized Fano inequality: ℙ[d(Ẑ, Z) > d] ≥ 1 − (I(Z; X̂) + 1)/log(M/M_d)
-- statement:
--   Let $\mathcal H$ be a finite hypothesis class of cardinality $M$ and let $Z$ be drawn uniformly from $\mathcal H$. Let $\hat X$ take values in a finite set $\mathcal X$, with $\mathbb P(\hat X=x\mid Z=h)=W(h,x)$ for a stochastic kernel $W$, and let the estimate $\hat Z\in\mathcal H$ be drawn from a stochastic kernel $\kappa$ applied to $\hat X$ alone, so that $Z\to\hat X\to\hat Z$ is a Markov chain. Let $d:\mathcal H\times\mathcal H\to\mathbb R_+$ and $d>0$. For $h\in\mathcal H$ let $B_d(h)=\{h'\in\mathcal H\mid d(h,h')\le d\}$ and $M_d=\max_{h\in\mathcal H}|B_d(h)|$. If $M_d<M$, then
--   $$
--   \mathbb P\big[d(\hat Z,Z)>d\big]\;\ge\;1-\frac{I(Z;\hat X)+1}{\log(M/M_d)} ,
--   $$
--   where $I(Z;\hat X)$ is the mutual information (natural logarithm) of the joint law $\mathbb P(Z=h,\hat X=x)=W(h,x)/M$.
--
--   This is the generalized Fano inequality the paper takes from Lemma 20 of [3]: an estimator counts as successful when it lands within distance $d$ of the truth, and the inequality bounds the success probability by the information the data carry about the hypothesis. It is the engine of the impossibility result.
--
--   **Formalization Note** The observation space $\hat X$ is finite (the application has $\hat X=(A,B)$, a finite set). The Markov chain is built in: $Z$ uniform, $\hat X$ drawn from $W(Z,\cdot)$, $\hat Z$ drawn from $\kappa(\hat X,\cdot)$. No metric axioms on $d$ are assumed; the event uses $d(\hat Z,Z)$ with $\hat Z$ first, matching $B_d(h)$, whose centre is the first argument. The hypothesis $M_d<M$ is added: with $M_d=M$ the page's bound divides by $\log 1=0$, and Lean's $x/0=0$ would turn it into $\mathbb P\ge1$. If $M_d=0$, Lean's $\log(M/0)=0$ makes the right side $1$, which is then the true error probability.
-- source:
--   Hall, Massoulié, Partial Recovery in the Graph Alignment Problem, arXiv:2007.00533v5, pp. 10–11, Theorem 3.1 (Lemma 20 in [3])

import Mathlib
import Definitions.Def_GraphAlignment_Impossible_InfoMeasures

namespace GraphAlignment.Impossible

open Finset

theorem theorem_3_1 {H X : Type*} [Fintype H] [Nonempty H] [DecidableEq H] [Fintype X]
    (W : StochKernel H X) (κ : StochKernel X H)
    (dist : H → H → ℝ) (hdist : ∀ h h', 0 ≤ dist h h') (d : ℝ) (hd : 0 < d)
    (hMd : (univ.sup fun h : H => (univ.filter fun h' => dist h h' ≤ d).card) < Fintype.card H) :
    1 - (mutualInfo (fun h x => W.k h x / (Fintype.card H : ℝ)) + 1) /
        Real.log ((Fintype.card H : ℝ) /
          ((univ.sup fun h : H => (univ.filter fun h' => dist h h' ≤ d).card : ℕ) : ℝ)) ≤
      ∑ h, ∑ x, ∑ h', (1 / (Fintype.card H : ℝ)) * W.k h x * κ.k x h' *
        (if d < dist h' h then 1 else 0) := by sorry

end GraphAlignment.Impossible
