-- Prove2me | Theorems.Thm_MinorFreeSTC_Main_lemma_5
-- name    : MinorFreeSTC.Main.lemma_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:18:23.530073+00:00
-- url     : https://prove2.me/theorems/35513e4a-ccca-4f24-b76c-573cd27ad3d7
-- title:
--   Lemma 5 — the conflict graph X of a strong (α,τ)-sparse partition has |E(X[S])| ≤ |S|·O(τ r √log r)
-- statement:
--   There is a universal constant $c>0$ such that the following holds. Let $G$ be a connected $K_r$-minor-free weighted graph (weights in $[1,n^k]$), let $\Delta>0$, $\alpha,\tau\ge1$, and let $\mathcal P$ be a $\Delta$-diameter strong $(\alpha,\tau)$-sparse partition of $G$. Let $X$ be its conflict graph: vertex set $\mathcal P$, with distinct $P,Q$ adjacent when $B_G(P,\Delta/(2\alpha))\cap B_G(Q,\Delta/(2\alpha))\neq\emptyset$. Then for every $S\subseteq\mathcal P$
--   $$|E(X[S])|\ \le\ |S|\cdot c\,\tau\, r\sqrt{\log_2 r}.$$
--
--   The density bound lets Lemma 4 colour $X$ with $O(\tau r\sqrt{\log r})$ colours.
--
--   Differences from the source:
--   - reading: O(τ r √log r) → one explicit existentially quantified universal constant, chosen before every other quantity; reason: p. 13: O(·) has universal hidden constants unless otherwise stated
--   - encoding: 'Let G and P be as in Lemma 4' (p. 19): ∆ > 0 and α, τ ≥ 1 → hypotheses 0 < ∆, 1 ≤ α, 1 ≤ τ; reason: the conflict graph is defined in Lemma 4's context
--   - encoding: graph (with the standing assumption 'we will assume all input graphs are connected', p. 14) → hypothesis `Connected G` (d_G(u, v) < ∞ for all u, v); reason: standing assumption of §3.1 made explicit
--   - encoding: 'we will assume … w(e) ∈ [1, poly(n)]' (p. 13, standing for §§4–9.1) → hypothesis `AspectBounded G k` (1 ≤ w(e) ≤ n^k) for an arbitrary k : ℕ; running-time constants may depend on k; reason: standing assumption of §3.1 made explicit; §9.2 removes it only for the final theorem
--   - encoding: |E(X[S])| → half the number of ordered adjacent pairs in S × S (`inducedEdgeCount`); reason: each unordered edge is counted once
-- source:
--   Filtser, Fletcher, Hershkowitz, Milenković, (1 + ϵ)-Distortion Spanning Tree Covers of Minor-Free Graphs with Size O(log log n), STOC 2027 submission (manuscript sha256 f475e254…), p. 19, Lemma 5

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_MinorFreeSTC_Main_Graphs
import Definitions.Def_MinorFreeSTC_Main_Covers
import Definitions.Def_MinorFreeSTC_Main_Structures

set_option autoImplicit false

open scoped ENNReal

namespace MinorFreeSTC.Main

open ARTreeCover

/-- **Lemma 5** (p. 19). There is a universal `c` such that for every `K_r`-minor-free weighted
graph `G`, every `∆`-diameter strong `(α, τ)`-sparse partition `P` of `G` (`∆ > 0`, `α, τ ≥ 1`)
with conflict graph `X`, and every `S ⊆ P`: `|E(X[S])| ≤ |S| · c τ r √(log r)`. -/
theorem lemma_5 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : WGraph V) (r k : ℕ)
        (P : Finset (Finset V)) (Δ α τ : ℝ),
        Connected G → MinorFree G r → AspectBounded G k → 0 < Δ → 1 ≤ α → 1 ≤ τ →
        IsStrongSparsePartition G P Δ α τ →
        ∀ S ⊆ P, (inducedEdgeCount (conflictGraph G P Δ α) S : ℝ) ≤
          S.card * (c * τ * r * Real.sqrt (Real.logb 2 r)) := by sorry

end MinorFreeSTC.Main
