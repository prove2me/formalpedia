-- Prove2me | Theorems.Thm_MildHamilton_Main_lemma_3_1
-- name    : MildHamilton.Main.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:51:10.939941+00:00
-- url     : https://prove2.me/theorems/edb77715-d249-41e8-ac75-c19fbe3a1a9a
-- title:
--   Lemma 3.1, p. 6 — connecting lemma (corrected: 0 < ∆)
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $G$ be a graph and $R\subseteq V(G)$ with $|R|\ge3$. Suppose $G[R]$ is $p$-cut-dense, write $\Delta=\Delta(G[R])$, and assume $p|R|\ge\gamma\Delta$ for some $0<\gamma\le1$ and $\Delta>0$. Let $(a_i,b_i)_{i=1}^k$ be pairs of vertices in $V(G)\setminus R$, and let $T=\{a_i,b_i:i\in[k]\}$. Let $\beta\in(0,1)$ and suppose that every vertex occurs at most $10$ times among $a_1,b_1,\dots,a_k,b_k$, that $d_G(x,R)\ge\beta\Delta$ for every $x\in T$, and that
--
--   $$d_G(v,T)\le\frac{\beta\gamma^2\Delta}{C\log(2|R|)}\quad\text{for every }v\in R.$$
--
--   Then there are $a_i$–$b_i$ paths $P_i$, $i\in[k]$, whose internal vertex sets are pairwise disjoint and contained in $R$, and such that $|P_i|\le(C/\gamma)\log(2|R|)$ for every $i$.
--
--   This lemma embeds the connections of a Hamilton router in a random reservoir.
--
--   Differences from the source:
--   - correction: no lower bound on Δ = Δ(G[R]) → the hypothesis 0 < Δ(G[R]); reason: the printed statement is false at Δ = 0: take five isolated vertices, R three of them, k = 1, (a_1, b_1) the other two, p = 0, γ = 1, β = 1/2; every printed hypothesis holds and no a_1–b_1 path exists; the proof divides by βΔ on p. 7
--   - encoding: |P_i|, a graph G → Walk.length of P_i, with V a finite type; reason: the vertex count exceeds the length by 1, which C absorbs because log 6 / γ > 1; graphs are finite throughout the paper
-- source:
--   Alp Muyesser, STOC 2027 submission #233 (October 2026), Lemma 3.1, p. 6

import Mathlib
import Definitions.Def_MildHamilton_Main_Spectral

namespace MildHamilton.Main

open Classical in
/-- Lemma 3.1, the connecting lemma (Muyesser, STOC 2027 submission #233, p. 6), corrected by
`0 < Δ(G[R])`: the printed statement fails on the edgeless graph. `T` is `{a_i, b_i : i ∈ [k]}`, and
occurrences among `a_1, b_1, …, a_k, b_k` are counted with multiplicity. -/
theorem lemma_3_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (R : Finset V) (p γ β : ℝ)
      (k : ℕ) (a b : Fin k → V) (T : Finset V),
      3 ≤ R.card → IsCutDense (G.induce (R : Set V)) p →
      0 < inducedMaxDegree G R →
      0 < γ → γ ≤ 1 → γ * (inducedMaxDegree G R : ℝ) ≤ p * (R.card : ℝ) →
      (∀ i, a i ∉ R ∧ b i ∉ R) →
      T = Finset.univ.image a ∪ Finset.univ.image b →
      0 < β → β < 1 →
      (∀ x : V, (Finset.univ.filter fun i => a i = x).card +
        (Finset.univ.filter fun i => b i = x).card ≤ 10) →
      (∀ x ∈ T, β * (inducedMaxDegree G R : ℝ) ≤ (nbrCount G x R : ℝ)) →
      (∀ v ∈ R, (nbrCount G v T : ℝ) ≤
        β * γ ^ 2 * (inducedMaxDegree G R : ℝ) / (C * Real.log (2 * (R.card : ℝ)))) →
      ∃ P : ∀ i, G.Walk (a i) (b i),
        (∀ i, (P i).IsPath) ∧
        (∀ i, internalVerts (P i) ⊆ R) ∧
        (∀ i j, i ≠ j → Disjoint (internalVerts (P i)) (internalVerts (P j))) ∧
        ∀ i, ((P i).length : ℝ) ≤ C / γ * Real.log (2 * (R.card : ℝ)) := by sorry

end MildHamilton.Main
