-- Prove2me | Theorems.Thm_HDXConc_lemma_3_3
-- name    : HDXConc.lemma_3_3
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T15:58:43.596732+00:00
-- url     : https://prove2.me/theorems/5290848f-026e-41f7-912a-9cc31dad7968
-- title:
--   Lemma 3.3, p.16 — reweighting by $g(u)g(v)$ costs at most $\max g/\min g$
-- statement:
--   Let $(W,w)$ be a finite weighted graph with symmetric nonnegative weights and positive degrees, whose random walk $S$ satisfies $\lambda_2(S)\le\lambda$ for some $\lambda\ge0$. Let $g:W\to(0,\infty)$, and let $S'$ be the random walk for the weights $w'(u,v)=w(u,v)g(u)g(v)$. Then
--
--   $$\lambda_2(S')\le\frac{\max_{u\in W}g(u)}{\min_{v\in W}g(v)}\cdot\lambda.$$
--
--   Each walk is measured against its own degrees. The lemma controls how the spectrum of a link moves when the top density is exponentially tilted.
--
--   Differences from the source:
--   - generalization: a graph (the sentence before the lemma: connected) without loops → symmetric nonnegative weights on a finite set with positive degrees at every vertex; loops are not excluded; reason: a connected graph with at least two vertices has positive degrees, and the printed case is an instance
--   - reading: g : V → R+ → 0 < g v on W; reason: min g appears in a denominator
--   - encoding: λ₂(S) ≤ λ and λ₂(S′) ≤ … → SecondEigLE W w λ and SecondEigLE W w′ …; reason: Courant–Fischer gives the equivalence for positive degrees and |W| ≥ 2; at |W| = 1 the predicate has only g = 0
--   - encoding: max_{u∈V} g(u), min_{v∈V} g(v) → W.sup' hW g and W.inf' hW g with W nonempty; reason: a maximum and a minimum over a nonempty finite set
-- source:
--   Das, Hopkins, Ray, Tung, Concentration on HDX: Simplified and Optimized, STOC 2027 submission (manuscript sha256 ea5bee5f…), Lemma 3.3, p.16 (proof pp.29–30)

import Mathlib
import Definitions.Def_HDXConc_SecondEigLE

namespace HDXConc

/-- Lemma 3.3, p.16 (proof pp.29–30): if `λ₂(S) ≤ lam` for the random walk `S` of a weighted graph `(W, w)` and
some `lam ≥ 0`, and `w' {u, v} = w {u, v} g(u) g(v)` for some positive `g`, then the random walk `S'` of `(W, w')`
has `λ₂(S') ≤ (max_u g(u) / min_v g(v)) · lam`.

Das, Hopkins, Ray, Tung, *Concentration on HDX: Simplified and Optimized*, STOC 2027 submission (manuscript
sha256 ea5bee5f…).

**Formalization Note.** `SecondEigLE` uses the degrees of the weights it is given, so each walk is measured against
its own stationary weights. The graph is a finite vertex set `W` with symmetric nonnegative weights and positive
degrees. This is weaker than the "connected" of the sentence before the lemma, and the zero weights are the non-edges;
loops are not excluded. -/
theorem lemma_3_3 {V : Type*} (W : Finset V) (hW : W.Nonempty) (w : V → V → ℝ) (lam : ℝ)
    (hlam : 0 ≤ lam)
    (hsymm : ∀ u ∈ W, ∀ v ∈ W, w u v = w v u)
    (hnonneg : ∀ u ∈ W, ∀ v ∈ W, 0 ≤ w u v)
    (hdeg : ∀ v ∈ W, 0 < weightedDeg W w v)
    (g : V → ℝ) (hg : ∀ v ∈ W, 0 < g v)
    (hS : SecondEigLE W w lam) :
    SecondEigLE W (fun u v => w u v * g u * g v) ((W.sup' hW g / W.inf' hW g) * lam) := by sorry

end HDXConc
