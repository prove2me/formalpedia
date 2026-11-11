-- Prove2me | Theorems.Thm_FracColorLocal_KrFree_lemma_5_3
-- name    : FracColorLocal.KrFree.lemma_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:11:41.449198+00:00
-- url     : https://prove2.me/theorems/a8d135c7-2e1c-4ce7-b079-6931815a2056
-- title:
--   Lemma 5.3 (existence statement) — Kang's neighbourhood restriction: C ⊆ Y with w(C) ≥ Q^{−(r−2)}w(Y) and w(N(v)∩C) ≤ w(C)/Q
-- statement:
--   Let $r\ge2$, let $G$ be a finite $K_r$-free graph with positive real vertex weights $w$, let $Y\subseteq V(G)$ be nonempty and $Q\ge1$. There is a nonempty set $C\subseteq Y$ such that
--
--   $$w(C)\ \ge\ Q^{-(r-2)}\,w(Y),\qquad w(N(v)\cap C)\ \le\ w(C)/Q\quad(v\in C).$$
--
--   This is the only place where $K_r$-freeness is used, and it is the source of the linear dependence on $r$ in Theorem 1.7.
--
--   Differences from the source:
--   - reading: the lemma's last sentence (for rational $w,Q$ a deterministic polynomial-time algorithm finds $C$) → not stated; reason: it belongs to the algorithmic results (Theorem 1.9, Corollary 1.10), which this mission does not formalize; the existence statement is stated in full.
-- source:
--   Davies, Dhawan, Methuku, Nguyen, Seo, Fractional colorings of K_r-free graphs with local demands, arXiv:2611.04297 (PDF sha256 b3f2dcce…), p. 21 (PDF 22), Lemma 5.3 (existence statement)

import Mathlib
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph

open OAI.CliqueFreeIndependence.WeightedGraph

namespace FracColorLocal.KrFree

/-- Lemma 5.3 (Kang's neighbourhood restriction), existence statement. -/
theorem lemma_5_3 {V : Type*} [Fintype V] [DecidableEq V] (r : ℕ) (hr : 2 ≤ r) (G : SimpleGraph V)
    (hG : G.CliqueFree r) (w : V → ℝ) (hw : ∀ v, 0 < w v) (Y : Finset V) (hY : Y.Nonempty)
    (Q : ℝ) (hQ : 1 ≤ Q) :
    ∃ C : Finset V, C ⊆ Y ∧ C.Nonempty ∧
      (Q ^ (r - 2))⁻¹ * mass w Y ≤ mass w C ∧
      ∀ v ∈ C, mass w (neighbors G v ∩ C) ≤ mass w C / Q := by sorry

end FracColorLocal.KrFree
