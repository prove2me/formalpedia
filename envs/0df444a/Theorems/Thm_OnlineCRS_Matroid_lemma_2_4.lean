-- Prove2me | Theorems.Thm_OnlineCRS_Matroid_lemma_2_4
-- name    : OnlineCRS.Matroid.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:24:43.354417+00:00
-- url     : https://prove2.me/theorems/5b14b532-9cbf-426b-8b1c-50a1c286a3e2
-- title:
--   Lemma 2.4, p. 11 — Σ_e x_e Pr[e ∈ span(R(x) ∪ S)] ≤ b·(x(N) + (1 − b) rank(S)), strict if S ≠ ∅
-- statement:
--   Let $M$ be a matroid on the finite ground set $N$ with rank function $\operatorname{rank}$ and span operator $\operatorname{span}$, let $b\in[0,1]$, and let $x\in b\cdot P_{\mathcal F}$, where $P_{\mathcal F}=\{x\in\mathbb R^N_{\ge0} : x(S)\le\operatorname{rank}(S)\ \forall S\subseteq N\}$ is the matroid polytope. Let $R(x)$ be the random set containing each $e\in N$ independently with probability $x_e$, and let $S=S_{|N|}$ be the set produced by the refinement procedure: $S_0=\varnothing$ and $S_i=\{e\in N : \Pr[e\in\operatorname{span}((R(x)\cup S_{i-1})\setminus\{e\})]>b\}$. Then
--
--   $$\sum_{e\in N}x_e\Pr[e\in\operatorname{span}(R(x)\cup S)]\le b\cdot\bigl(x(N)+(1-b)\operatorname{rank}(S)\bigr).$$
--
--   Moreover, if $M$ has no loops and $S\ne\varnothing$, the inequality is strict.
--
--   This is the key technical estimate of the termination analysis of the chain construction: combined with the base-polytope normalization it shows that the first set of the chain is a proper subset of the ground set.
--
--   **Formalization Note** The ground set is the whole finite type ($M.E=$ univ) and the rank is the real number $\operatorname{rank}(S)=|$basis of $S|$. The probability is the finite sum $\sum_A\Pr[R(x)=A]\,[e\in\operatorname{span}(A\cup S)]$; unlike in the definition of $S_i$, $e$ is not removed. The hypothesis is $x\in b\cdot P_{\mathcal F}$, the hypothesis the proof uses ("using $x\in b\cdot P_{\mathcal I}$"), which includes the section's standing case $x\in b\cdot P_{\mathcal B}$. Looplessness is added to the strict clause only: for a single loop $e$ and $b<1$ one has $x_e=0$, $S=\{e\}$ and both sides equal $0$, so the printed strict clause fails there; the non-strict clause is stated for every matroid.
-- source:
--   arXiv:1508.00142v2, Lemma 2.4, p. 11

import Mathlib
import Definitions.Def_OnlineCRS_Matroid_Construction

open scoped Pointwise

namespace OnlineCRS.Matroid

/-- arXiv:1508.00142v2, Lemma 2.4, p. 11. The non-strict inequality holds for every matroid; the strict
part is stated for loopless matroids (disclosed correction: it fails for a single loop). -/
theorem lemma_2_4 {α : Type} [Fintype α] [DecidableEq α]
    (M : Matroid α) (hE : M.E = Set.univ)
    (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (x : α → ℝ) (hx : x ∈ b • matroidPolytope M) :
    (∑ e : α, x e * spanWithProb M x (Sfin M x b) e ≤
        b * ((∑ e : α, x e) + (1 - b) * rank M (Sfin M x b))) ∧
      (M.Loopless → Sfin M x b ≠ ∅ →
        ∑ e : α, x e * spanWithProb M x (Sfin M x b) e <
          b * ((∑ e : α, x e) + (1 - b) * rank M (Sfin M x b))) := by sorry

end OnlineCRS.Matroid
