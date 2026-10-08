-- Prove2me | Theorems.Thm_LambdaCoalescent_CoagFrag_lemma_9_exists
-- name    : LambdaCoalescent.CoagFrag.lemma_9_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:21:05.782417+00:00
-- url     : https://prove2.me/theorems/0bf703f4-ee0a-4ce4-97c0-bf73f0acc6e8
-- title:
--   Lemma 9, pp. 1876–1877 — for 0 ≤ α < 1, θ > −α an exchangeable random partition with EPF p_{α,θ} of (15) exists
-- statement:
--   Let $0\le\alpha<1$ and $\theta>-\alpha$ (condition (14)). For $n_1,\dots,n_k\ge1$ with $n=n_1+\dots+n_k$, let
--   $$p_{\alpha,\theta}(n_1,\dots,n_k)=\frac{[\theta/\alpha]_k}{[\theta]_n}\prod_{i=1}^{k}-[-\alpha]_{n_i},\qquad [x]_m=\prod_{i=1}^{m}(x+i-1),$$
--   with the factors of $\theta$ and $\alpha$ cancelled before evaluation when $\alpha=0$ or $\theta=0$. Then there is a probability measure $\mu$ on the space $\mathcal P_\infty$ of partitions of $\mathbb N$ such that for every $n$ and every partition $\{B_1,\dots,B_k\}$ of $[n]$,
--   $$\mu\{\pi\in\mathcal P_\infty: R_n\pi=\{B_1,\dots,B_k\}\}=p_{\alpha,\theta}(|B_1|,\dots,|B_k|).$$
--   In words: an exchangeable random partition of $\mathbb N$ with EPF (15), an $(\alpha,\theta)$ partition, exists.
--
--   This is the existence part of Lemma 9, the two-parameter family of exchangeable partitions (Ewens' family for $\alpha=0$). It guarantees that the hypotheses of Theorem 12, four laws with prescribed $(\alpha,\theta)$ EPFs, can be met.
--
--   **Formalization Note** Only the existence of a law with EPF (15) is formalized. The rest of Lemma 9 (the block frequencies in order of least elements are strictly positive, sum to $1$ and have the stick-breaking form (12) with independent beta$(1-\alpha,\theta+n\alpha)$ factors (13), and the converse) is not stated. Lemma 9 is cited by the paper from [32], [33]. The EPF is the cancelled form fixed in the Setting module.
-- source:
--   Pitman, Coalescents with multiple collisions, Ann. Probab. 27 (1999), pp. 1876–1877, Lemma 9, (14), (15), and the paragraph after it

import Mathlib
import Definitions.Def_LambdaCoalescent_CoagFrag_Setting

namespace LambdaCoalescent.CoagFrag

open MeasureTheory

theorem lemma_9_exists (α θ : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hθ : -α < θ) :
    ∃ μ : Measure LambdaCoalescent.Rates.PInf, IsProbabilityMeasure μ ∧ IsEPFLaw (pdEPF α θ) μ := by sorry

end LambdaCoalescent.CoagFrag
