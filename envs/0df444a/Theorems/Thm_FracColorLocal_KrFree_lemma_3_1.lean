-- Prove2me | Theorems.Thm_FracColorLocal_KrFree_lemma_3_1
-- name    : FracColorLocal.KrFree.lemma_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:12:28.389357+00:00
-- url     : https://prove2.me/theorems/b5d361e1-f6a5-464a-a2c6-e70cfd55c8cc
-- title:
--   Lemma 3.1 — a φ-coloring exists iff α_u(G) ≥ Σ u(v)φ(v) for every u ≥ 0; positive u suffice
-- statement:
--   Let $G$ be a finite graph on $V$ and $\varphi:V\to[0,1]$ a demand function. Then $G$ admits a $\varphi$-coloring (a probability distribution on independent sets with $\mathbb P(v\in I)\ge\varphi(v)$ for all $v$) if and only if
--
--   $$\alpha_u(G)\ \ge\ \sum_{v}u(v)\varphi(v)\qquad\text{for every }u:V\to[0,\infty),$$
--
--   where $\alpha_u(G)=\max\{u(I):I\text{ independent}\}$. It suffices to check this inequality for positive $u$: a $\varphi$-coloring also exists if and only if the inequality holds for every $u:V\to(0,\infty)$.
--
--   This is the linear-programming duality criterion through which weighted independent-set bounds (Theorem 1.7) yield distributions meeting local demands (Corollary 1.8, Theorem 1.5).
--
--   Differences from the source:
--   - reading: "It suffices to check this inequality for positive u" → a second equivalence with $u>0$ in place of $u\ge 0$; reason: the forward direction is the restriction of the first equivalence, so the two statements say the same.
-- source:
--   Davies, Dhawan, Methuku, Nguyen, Seo, Fractional colorings of K_r-free graphs with local demands, arXiv:2611.04297 (PDF sha256 b3f2dcce…), p. 16 (PDF 17), Lemma 3.1

import Mathlib
import Definitions.Def_FracColorLocal_KrFree_PhiColoring

namespace FracColorLocal.KrFree

/-- Lemma 3.1: a `φ`-coloring exists iff `α_u(G) ≥ ∑_v u(v) φ(v)` for every `u ≥ 0`;
positive `u` suffice. -/
theorem lemma_3_1 {V : Type*} [Fintype V] (G : SimpleGraph V) (φ : V → ℝ)
    (hφ : IsDemandFunction φ) :
    (HasPhiColoring G φ ↔
      ∀ u : V → ℝ, (∀ v, 0 ≤ u v) → ∑ v, u v * φ v ≤ weightedIndepNumber G u) ∧
    (HasPhiColoring G φ ↔
      ∀ u : V → ℝ, (∀ v, 0 < u v) → ∑ v, u v * φ v ≤ weightedIndepNumber G u) := by sorry

end FracColorLocal.KrFree
