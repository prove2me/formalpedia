-- Prove2me | Theorems.Thm_LambdaCoalescent_CoagFrag_lemma_35
-- name    : LambdaCoalescent.CoagFrag.lemma_35
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:21:13.850525+00:00
-- url     : https://prove2.me/theorems/0d257542-253b-4e92-9640-27754c0541b0
-- title:
--   Lemma 35, p. 1898 — Π¹ is a p̂-fragmentation of Π² with law p₂ iff P(Π¹_n = π¹, Π²_n = π²) = ∏ p̂(a_{i,1},…,a_{i,j_i}) p₂(b₁,…,b_k)
-- statement:
--   Let $\Pi^1_\infty,\Pi^2_\infty$ be two random partitions of $\mathbb N$ on a probability space $(\Omega,\mathbb P)$, with restrictions $\Pi^i_n=R_n\Pi^i_\infty$ to $[n]$. Let $p_2$ and $\hat p$ be EPFs of exchangeable laws $\mu_2$ and $\hat\nu$ on $\mathcal P_\infty$. The following are equivalent.
--
--   1. $\Pi^2_\infty$ has law $\mu_2$, and given $\Pi^2_\infty=\pi$, $\Pi^1_\infty$ is distributed as the fragmentation of $\pi$ whose restriction to the $m$-th block of $\pi$ is that of $\Gamma^{(m)}$, for independent $\Gamma^{(1)},\Gamma^{(2)},\dots$ with law $\hat\nu$ (the kernel $\hat p$-FRAG$(\pi,\cdot)$ of Definition 11). Equivalently, for every measurable $S\subseteq\mathcal P_\infty\times\mathcal P_\infty$,
--   $$\mathbb P\big((\Pi^1_\infty,\Pi^2_\infty)\in S\big)=\Big(\mu_2\otimes\hat\nu^{\otimes\mathbb N}\Big)\{(\pi,\Gamma): (\text{fragmentation of }\pi\text{ by }\Gamma,\ \pi)\in S\}.$$
--   2. For every $n\ge1$ and every pair $\pi^1=\{A_1,\dots,A_K\}$, $\pi^2=\{B_1,\dots,B_k\}$ of partitions of $[n]$ such that $\pi^1$ refines $\pi^2$, obtained by breaking each $B_i$ into $j_i\ge1$ blocks of sizes $a_{i,1},\dots,a_{i,j_i}$,
--   $$\mathbb P(\Pi^1_n=\pi^1,\ \Pi^2_n=\pi^2)=\prod_{i=1}^{k}\hat p(a_{i,1},\dots,a_{i,j_i})\;p_2(b_1,\dots,b_k),\qquad b_i=|B_i|.\tag{63}$$
--
--   This is the fragmentation analogue of Lemma 34; together they reduce Theorem 12 to an identity between EPFs.
--
--   **Formalization Note** As in Lemma 34, condition (i) is the equality of joint laws through (outer) measures of preimages of measurable sets, with the clause "$\Pi^2$ has law $\mu_2$" kept. The fragmenting partitions are one sample from the infinite product $\hat\nu^{\otimes\mathbb N}$ (`Measure.infinitePi`), so they are independent and identically distributed; $\Gamma^{(m)}$ is Lean's `Γ (m-1)`, applied to the block of 0-based index $m-1$ in order of least elements. (63) is required only for refining pairs, as on the page. The nested sizes $(a_{i,\ell})$ are a multiset of multisets, $\hat p$ and $p_2$ being symmetric.
-- source:
--   Pitman, Coalescents with multiple collisions, Ann. Probab. 27 (1999), p. 1898, Lemma 35, (63)

import Mathlib
import Definitions.Def_LambdaCoalescent_CoagFrag_Setting

namespace LambdaCoalescent.CoagFrag

open MeasureTheory

theorem lemma_35 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₁ X₂ : Ω → LambdaCoalescent.Rates.PInf) (hX₁ : Measurable X₁) (hX₂ : Measurable X₂)
    (p₂ phat : Multiset ℕ → ℝ) (μ₂ νhat : Measure LambdaCoalescent.Rates.PInf)
    [IsProbabilityMeasure μ₂] [IsProbabilityMeasure νhat]
    (hμ₂ : IsEPFLaw p₂ μ₂) (hνhat : IsEPFLaw phat νhat) :
    (P.map X₂ = μ₂ ∧
        ∀ S : Set (LambdaCoalescent.Rates.PInf × LambdaCoalescent.Rates.PInf), MeasurableSet S →
          P {ω | (X₁ ω, X₂ ω) ∈ S} =
            (μ₂.prod (Measure.infinitePi (fun _ : ℕ => νhat))) {y | (frag y.1 y.2, y.1) ∈ S}) ↔
      ∀ (n : ℕ) (π₁ π₂ : Setoid (Fin n)), π₁ ≤ π₂ →
        P.real {ω | restrict n (X₁ ω) = π₁ ∧ restrict n (X₂ ω) = π₂} =
          ((fragSizes π₁ π₂).map phat).prod * p₂ (blockSizes π₂) := by sorry

end LambdaCoalescent.CoagFrag
