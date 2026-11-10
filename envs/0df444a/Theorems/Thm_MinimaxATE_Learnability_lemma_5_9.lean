-- Prove2me | Theorems.Thm_MinimaxATE_Learnability_lemma_5_9
-- name    : MinimaxATE.Learnability.lemma_5_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:00:21.383745+00:00
-- url     : https://prove2.me/theorems/effa175e-e00f-4a3d-a744-4d2968541eb0
-- title:
--   Lemma 5.9 (Alon) — a large pairwise sign-separated family over $\{-q,\dots,q\}$ shatters some $(I,A)$ with $|I|\ge k/(C_A\log_2^2q)$
-- statement:
--   There is an absolute constant $C_A>0$ such that the following holds. Fix $N,q\in\mathbb N_+$ and let $F$ be a set of functions $f:[N]\to\{-q,\dots,q\}$. Two functions $f_1,f_2$ are **separated** if $\operatorname{sgn}(f_1(j))\ne\operatorname{sgn}(f_2(j))$ for some $j\in[N]$. For $I\subseteq[N]$ and values $A=(u^-_i,u^+_i)_{i\in I}$ with $u^-_i\in-[q]=\{-q,\dots,-1\}$ and $u^+_i\in[q]=\{1,\dots,q\}$, $F$ **shatters** $(I,A)$ if for every $g$ on $I$ with $g(i)\in\{u^-_i,u^+_i\}$ there is $f\in F$ with $f|_I=g$. If $F$ is pairwise separated and
--   $$|F|>\sum_{i=0}^{k-1}\binom Ni,$$
--   then there are $I\subseteq[N]$ and values $A$ such that $F$ shatters $(I,A)$ and
--   $$|I|\ge\frac{k}{C_A\log_2^2q}.$$
--
--   A multi-valued Sauer–Shelah lemma (Alon); it is the combinatorial engine of Lemma 1.9.
--
--   **Formalization Note.** $[N]$ is `Fin N`, functions are `ℤ`-valued, $\operatorname{sgn}$ is `Int.sign` ($\operatorname{sgn}0=0$), $k\in\mathbb N$. The choice $g$ is encoded by a boolean per index (`true` picks $u^+_i$).
--
--   Differences from the source:
--   - encoding: k/(C_A log₂² q) at q = 1, where log₂ 1 = 0 and the printed bound is undefined → real division, so the bound reads |I| ≥ 0; reason: the printed k/0 is undefined; the case q = 1 is never used (Lemma 1.9's proof takes q ≥ 2).
--   - reading: I ⊂ [N] → I any finset of indices (I ⊆ [N]); reason: ⊂ is used for ⊆ in the paper (the proof of Lemma 1.9 may take I to be all coordinates).
--   - encoding: F shatters (I, A): every g : I → ∪{u⁻_i, u⁺_i} with g(i) ∈ {u⁻_i, u⁺_i} is f|_I for some f ∈ F → for every choice b : Fin N → Bool some f ∈ F has f i = (b i ? u⁺_i : u⁻_i) on I; reason: a choice of one of the two values at each i ∈ I is the same as such a g.
-- source:
--   Cai, Kalavasis, Mamali, Mehrotra, Zampetakis, Minimax Rates for Estimation of Average Treatment Effects in Observational Studies, STOC 2027 submission (manuscript sha256 89998c39…), p. 42 (PDF 44), Lemma 5.9 (citing Alon, Theorem 1)

import Mathlib

namespace MinimaxATE.Learnability

theorem lemma_5_9 : ∃ CA : ℝ, 0 < CA ∧
    ∀ (N q : ℕ), 1 ≤ N → 1 ≤ q →
    ∀ (F : Finset (Fin N → ℤ)), (∀ f ∈ F, ∀ j, -(q : ℤ) ≤ f j ∧ f j ≤ q) →
      (∀ f₁ ∈ F, ∀ f₂ ∈ F, f₁ ≠ f₂ → ∃ j, Int.sign (f₁ j) ≠ Int.sign (f₂ j)) →
    ∀ (k : ℕ), ∑ i ∈ Finset.range k, N.choose i < F.card →
      ∃ (I : Finset (Fin N)) (um up : Fin N → ℤ),
        (∀ i ∈ I, -(q : ℤ) ≤ um i ∧ um i ≤ -1 ∧ 1 ≤ up i ∧ up i ≤ q) ∧
        (∀ g : Fin N → Bool, ∃ f ∈ F, ∀ i ∈ I, f i = if g i then up i else um i) ∧
        (k : ℝ) / (CA * Real.logb 2 q ^ 2) ≤ I.card := by sorry

end MinimaxATE.Learnability
