-- Prove2me | Theorems.Thm_MinCostArbPacking_Main_lemma_5_2
-- name    : MinCostArbPacking.Main.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:45:34.752197+00:00
-- url     : https://prove2.me/theorems/21ab1e33-6053-486b-928f-505fa25df799
-- title:
--   Lemma 5.2 — price update and batch augmentation
-- statement:
--   **Lemma 5.2 (Price update and batch augmentation).** Assume $\deg^{in}_I(r)=0$, $\deg^{in}_I(v)\le k$ for $v\ne r$, the reduced graph of §3.1, and the price invariant (5.1). Let $h^+(v)=h(v)+\min\{\delta_v,L\}$ with $L=\max(\{0\}\cup\{\delta_v:\delta_v<\infty\})$ and $a^+(e)=c(e)-h^+(\mathrm{head}(e))$.
--
--   1. $I$ minimizes $a^+$ over all independent sets of $\mathcal G^k$.
--   2. If $\delta_u<+\infty$, then $h^+(u)=d_u$, and every shortest augmenting path $P$ from $u$ has
--   $$a^+(P)=a^+(I\oplus P)-a^+(I)=0.$$
--   3. After executing the proposals whose terminals belong to a compatible set $A'$, the resulting set $I'$ minimizes $a^+$ over all independent sets of $\mathcal G^k$.
--
--   It shows that the price invariant survives every phase.
--
--   Differences from the source:
--   - encoding: the standing assumptions of §3.1 and §5.1 (loops and arcs entering $r$ deleted; no arc of $I$ into $r$, indegree $\le k$ elsewhere; the price invariant (5.1)) → explicit hypotheses `NoLoopNoRootArc`, `inDeg I r = 0`, `inDeg I v ≤ k` (v ≠ r) and `PriceInv` (5.1); reason: the source states them once for §§3.1 and 5.1 (the algorithm keeps them); (5.1) implies that $I$ is cheapest for its indegree vector
-- source:
--   Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), §5.2, p.24, Lemma 5.2

import Mathlib
import Definitions.Def_MinCostArbPacking_Main_Exchange
set_option autoImplicit false

namespace MinCostArbPacking.Main

/-- Lemma 5.2 (Price update and batch augmentation), p.24, under (5.1) and the indegree invariants,
with `h⁺(v) = h(v) + min{δ_v, L}`:
(a) `I` minimizes `a⁺` over all independent sets of `𝒢^k`;
(b) if `δ_u < +∞`, then `h⁺(u) = d_u` and every shortest augmenting path `P` from `u` has
`a⁺(P) = 0`;
(c) after executing the proposals whose terminals form a compatible set `A'`, the resulting set
minimizes `a⁺` over all independent sets of `𝒢^k`. -/
theorem lemma_5_2 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : Digraph V E) (k : ℕ) (hk : 1 ≤ k) (r : V) (c : E → ℝ)
    (hG : G.NoLoopNoRootArc r) (h : V → ℝ) (I : Finset E) (hr : G.inDeg I r = 0)
    (hdeg : ∀ v, v ≠ r → G.inDeg I v ≤ k) (hinv : G.PriceInv k c h I) :
    G.PriceInv k c (G.hplus k c h I) I ∧
    (∀ u, G.delta k c h I u ≠ ⊤ →
      ((G.hplus k c h I u : ℝ) : EReal) = G.dCost k c I u ∧
        ∀ P, G.ShortestFrom k c I u P → pathCost (G.adj c (G.hplus k c h I)) I P = 0) ∧
    (∀ (u : Finset V → V) (P : Finset V → List E) (A' : Finset E),
      G.IsProposalSystem k r c I u P → G.Compatible k r I P A' →
        G.PriceInv k c (G.hplus k c h I) (G.execute k r I P A')) := by sorry

end MinCostArbPacking.Main
