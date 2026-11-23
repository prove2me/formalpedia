-- Prove2me | Theorems.Thm_HGASUndecidable_Main_theorem_2_3_computable_reduction
-- name    : HGASUndecidable.Main.theorem_2_3_computable_reduction
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:49:44.301204+00:00
-- url     : https://prove2.me/theorems/73bd812b-3f9f-4262-b060-bc30ac89f923
-- title:
--   The computable reduction from the halting set to a fixed HGAS problem
-- statement:
--   Fix the Diophantine data of Lemma 7.2, an admissible even compactification power $M$, and the rational constants $M_0,K_0$ of Lemma 9.4. There is a total computable function $f:\mathbb N\to\mathbb N$ such that, for every $e\in\mathbb N$,
--   $$
--   f(e)\in\mathrm{HGAS}(n_*,d_*)\quad\Longleftrightarrow\quad e\in K,
--   $$
--   where $n_*=n_s+n_h+3$ and $d_*=M+9$.
--
--   The code $f(e)$ is obtained by the finite rational-polynomial construction in steps (1)–(4) of the proof of Theorem 2.3. One computes $c(e)$, the gain $K_e$ and the terminating search index $m_e$, forms the compactified vector field (9.2) and quadratic reward (9.3), and applies Theorem 10.1 with $k=2$, dimensions $n_s+1,n_h+1$, and $D=M+3$. Proposition 9.5 and Theorem 10.1 give the displayed equivalence. No test of membership $e\in K$ is used by the algorithm.
-- source:
--   Shevchenko, Liu, Liu (2026), arXiv:2610.12434 (SHA-256 72e185f4750fe9bb72a2f146b2802fa13a97dcdd4f66e0e762b703dc7ddd77a8), proof of Theorem 2.3, steps (1)–(4), printed pp. 69–70 (PDF 71–72)

import Definitions.Def_HGASUndecidable_Main_SphereCodes

open Filter Topology MeasureTheory
open scoped BigOperators

namespace HGASUndecidable.Main

theorem theorem_2_3_computable_reduction (a : DiophantineData)
    (ha : DiophantineValid a) (M : ℕ) (hM : admissiblePower a M)
    (M₀ K₀ : ℚ) (hb : Bounds94 a M₀ K₀) :
    ∃ f : ℕ → ℕ, Computable f ∧
      ∀ e, HGAS (compactDim a) (M+9) (f e) ↔ haltingSet e := by sorry
