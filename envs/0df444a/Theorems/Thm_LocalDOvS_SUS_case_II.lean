-- Prove2me | Theorems.Thm_LocalDOvS_SUS_case_II
-- name    : LocalDOvS.SUS.case_II
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:25:32.063987+00:00
-- url     : https://prove2.me/theorems/c8c75f5d-28b1-46d5-9454-0b6a449948ac
-- title:
--   Case II, pp.ec16–ec17 — a Type-II Operation keeps an $\epsilon/2$-optimal point (corrected interval)
-- statement:
--   Let $f$ be discretely convex on $[N]$ and $\epsilon>0$. Let $S=\{x_0+js:0\le j<M\}\subseteq[N]$ with $M\ge3$ and step $s\ge1$, and let $x_L,x_U$ be integers with
--
--   $$
--   \min S-s\le x_L\le\min S,\qquad \max S\le x_U\le\max S+s,\qquad 1\le x_L,\ x_U\le N .
--   $$
--
--   Suppose that some global minimizer of $f$ on $[N]$ lies in $\{x_L,\dots,x_U\}$ and that $\max_Sf-\min_Sf\le M\epsilon/20$. Then the active set after a Type-II Operation, $S'=\{x_0+j\cdot2s:0\le j<\lceil M/2\rceil\}$, satisfies
--
--   $$
--   \min_{x\in S'}f(x)\le\min_{x\in X}f(x)+\frac\epsilon2 .
--   $$
--
--   The hypotheses are the facts available at a Type-II Operation in the proof of Theorem 2: the corrected interval of Lemma EC.8, the induction event on the interval, and (EC.13).
--
--   Differences from the source:
--   - correction: x_{L,k−1} = min S_{k−1} (Lemma EC.8 as printed), so [x_L, x_U] extends only to the right of S → min S − s ≤ x_L ≤ min S (corrected Lemma EC.8), so the minimizer may lie up to s to the left of min S; reason: with the printed bounds the induction fails (f = (9, 6, 3, 2.5, 3.2, 6, 9), S = {1, 3, 5, 7}, d = 2, x = 3, y = 5 excludes the minimizer 4); with the corrected bounds the left case is not covered by the printed application of Lemma EC.7 and is included here
--   - encoding: conclusion min_{y∈[M′]} g̃(2y − 1) − min_{x∈X} f(x) = min_{x∈S_k} f(x) − min_{x∈X} f(x) ≤ ϵ/2 → some j < ⌈M/2⌉ has f(x₀ + j · 2s) ≤ f(y) + ε/2 for all y ∈ [N]; reason: the same statement; avoids a minimum
--   - encoding: the induction events, Lemma EC.8 and (EC.13) used inside the proof → explicit hypotheses; reason: the lemma is the deterministic step of Case II
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, proof of Theorem 2, Case II, pp.ec16–ec17

import Mathlib
import Definitions.Def_LocalDOvS_SUS_DiscConvex

namespace LocalDOvS.SUS

/-- **Case II of the proof of Theorem 2, pp.ec16–ec17** (Zhang–Zheng–Lavaei,
arXiv:2012.02427v2), with the corrected interval of Lemma EC.8. Let `f` be convex on `[N]`,
`S = {x₀ + j·s : j < M} ⊆ [N]` with `M ≥ 3`, `s ≥ 1`, and bounds `x_L, x_U` with
`min S − s ≤ x_L ≤ min S`, `max S ≤ x_U ≤ max S + s`, `[x_L, x_U] ⊆ [N]`, such that some
global minimizer of `f` on `[N]` lies in `{x_L, …, x_U}` and `max_S f − min_S f ≤ M/20 · ε`.
Then after the Type-II Operation the new active set
`S' = {x₀ + j·2s : j < ⌈M/2⌉}` satisfies `min_{S'} f ≤ min_X f + ε/2`.

**Formalization Note.** The conclusion is "some point of `S'` is `ε/2`-optimal on `[N]`". The
hypotheses are exactly the two facts the proof has at this point: the corrected interval of
Lemma EC.8 and (EC.13). Because the corrected interval may extend up to `s` to the left of
`min S`, this includes a case the printed proof (which applies Lemma EC.7 with right padding
only) does not treat. `⌈M/2⌉ = (M + 1)/2`. -/
theorem case_II (N : ℕ) (f : ℕ → ℝ) (hf : DiscConvex N f) (ε : ℝ) (hε : 0 < ε)
    (x₀ s M xL xU : ℕ) (hM : 3 ≤ M) (hs : 1 ≤ s)
    (hS : ∀ j < M, x₀ + j * s ∈ Finset.Icc 1 N)
    (hL : (x₀ : ℤ) - s ≤ xL) (hL' : xL ≤ x₀)
    (hU : x₀ + (M - 1) * s ≤ xU) (hU' : xU ≤ x₀ + (M - 1) * s + s)
    (hLU : 1 ≤ xL ∧ xU ≤ N)
    (hmin : ∃ z ∈ Finset.Icc xL xU, ∀ y ∈ Finset.Icc 1 N, f z ≤ f y)
    (hspread : ∀ i < M, ∀ j < M, f (x₀ + i * s) - f (x₀ + j * s) ≤ (M : ℝ) / 20 * ε) :
    ∃ j < (M + 1) / 2, ∀ y ∈ Finset.Icc 1 N, f (x₀ + j * (2 * s)) ≤ f y + ε / 2 := by sorry

end LocalDOvS.SUS
