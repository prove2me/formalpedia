-- Prove2me | Theorems.Thm_LambdaCoalescent_CoagFrag_lemma_34
-- name    : LambdaCoalescent.CoagFrag.lemma_34
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:21:03.686572+00:00
-- url     : https://prove2.me/theorems/aebea741-7084-4e1d-9d8a-11ec81c99134
-- title:
--   Lemma 34, p. 1897 — Π² is a p-coagulation of Π¹ with law p₁ iff P(Π¹_n = π¹, Π²_n = π²) = p₁(a₁,…,a_K) p(j₁,…,j_k)
-- statement:
--   Let $\Pi^1_\infty,\Pi^2_\infty$ be two random partitions of $\mathbb N$ on a probability space $(\Omega,\mathbb P)$, with restrictions $\Pi^i_n=R_n\Pi^i_\infty$ to $[n]$. Let $p_1$ and $p$ be EPFs of exchangeable laws $\mu_1$ and $\nu$ on $\mathcal P_\infty$. The following are equivalent.
--
--   1. $\Pi^1_\infty$ has law $\mu_1$, and given $\Pi^1_\infty=\pi$, $\Pi^2_\infty$ is distributed as the $\gamma$-coagulation of $\pi$ for $\gamma\sim\nu$ (the kernel $p$-COAG$(\pi,\cdot)$ of Definition 5). Equivalently, for every measurable $S\subseteq\mathcal P_\infty\times\mathcal P_\infty$,
--   $$\mathbb P\big((\Pi^1_\infty,\Pi^2_\infty)\in S\big)=(\mu_1\otimes\nu)\{(\pi,\gamma): (\pi,\ \gamma\text{-coagulation of }\pi)\in S\}.$$
--   2. For every $n\ge1$ and every pair $\pi^1=\{A_1,\dots,A_K\}$, $\pi^2=\{B_1,\dots,B_k\}$ of partitions of $[n]$ such that $\pi^1$ refines $\pi^2$, with $j_i=\#\{\ell:A_\ell\subseteq B_i\}$ and $a_\ell=|A_\ell|$,
--   $$\mathbb P(\Pi^1_n=\pi^1,\ \Pi^2_n=\pi^2)=p_1(a_1,\dots,a_K)\,p(j_1,\dots,j_k).\tag{62}$$
--
--   The lemma turns the coagulation kernel into a closed formula for the finite-dimensional joint laws; together with Lemma 35 it reduces Theorem 12 to an identity between EPFs.
--
--   **Formalization Note** The conditional law "for all $\pi\in\mathcal P_\infty$" is meaningful only almost surely, so condition (i) is stated as the equality of the joint law of $(\Pi^1,\Pi^2)$ with the law of $(\pi,\gamma\text{-coag of }\pi)$ under $\mu_1\otimes\nu$, through (outer) measures of preimages of measurable sets; the clause "$\Pi^1$ has law $\mu_1$" is kept as on the page. "Exchangeable with distribution $p_1$" is `IsEPFLaw p₁ μ₁` for a probability measure `μ₁`. The random partitions are measurable maps $\Omega\to\mathcal P_\infty$. As on the page, (62) is required only for refining pairs; that the other pairs have probability $0$ follows from the total mass. Refinement is Mathlib's order on equivalence relations ($\pi^1\le\pi^2$: every $\pi^1$-relation is a $\pi^2$-relation). $(a_\ell)$ and $(j_i)$ are multisets ($p_1$, $p$ are symmetric). Labels are 0-based (see the Setting module).
-- source:
--   Pitman, Coalescents with multiple collisions, Ann. Probab. 27 (1999), p. 1897, Lemma 34, (62)

import Mathlib
import Definitions.Def_LambdaCoalescent_CoagFrag_Setting

namespace LambdaCoalescent.CoagFrag

open MeasureTheory

theorem lemma_34 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₁ X₂ : Ω → LambdaCoalescent.Rates.PInf) (hX₁ : Measurable X₁) (hX₂ : Measurable X₂)
    (p₁ p : Multiset ℕ → ℝ) (μ₁ ν : Measure LambdaCoalescent.Rates.PInf) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure ν]
    (hμ₁ : IsEPFLaw p₁ μ₁) (hν : IsEPFLaw p ν) :
    (P.map X₁ = μ₁ ∧
        ∀ S : Set (LambdaCoalescent.Rates.PInf × LambdaCoalescent.Rates.PInf), MeasurableSet S →
          P {ω | (X₁ ω, X₂ ω) ∈ S} = (μ₁.prod ν) {x | (x.1, coag x.1 x.2) ∈ S}) ↔
      ∀ (n : ℕ) (π₁ π₂ : Setoid (Fin n)), π₁ ≤ π₂ →
        P.real {ω | restrict n (X₁ ω) = π₁ ∧ restrict n (X₂ ω) = π₂} =
          p₁ (blockSizes π₁) * p (coagCounts π₁ π₂) := by sorry

end LambdaCoalescent.CoagFrag
