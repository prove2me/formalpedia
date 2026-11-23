-- Prove2me | Theorems.Thm_HGASUndecidable_Main_theorem_2_1_code_reduction
-- name    : HGASUndecidable.Main.theorem_2_1_code_reduction
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:30:50.718795+00:00
-- url     : https://prove2.me/theorems/44b53944-2ac1-46e3-90c4-b48a8413d611
-- title:
--   Total computable lift-and-pad reduction on raw field codes for Theorem 2.1
-- statement:
--   This is the code-level reduction used in the proof of Theorem 2.1. Fix positive integers $n_0,k_0$, a target dimension $n\geq\binom{n_0+k_0-1}{k_0}$, and $j\geq0$. There is one total computable function $r:\mathbb N\to\mathbb N$ on raw field codes such that, for every input code $e$, both equivalences
--   $$
--   e\in\mathrm{HGAS}(n_0,2k_0+1)\iff r(e)\in\mathrm{HGAS}(n,3+2j)
--   $$
--   and
--   $$
--   e\in\mathrm{HLS}(n_0,2k_0+1)\iff r(e)\in\mathrm{HLS}(n,3+2j)
--   $$
--   hold.
--
--   On valid inputs of the prescribed source dimension and degree, $r$ first applies the uniform degree-three lift of Theorem 2.4 and then the dimension-and-degree padding of Lemma 6.1. On every other input it returns a fixed invalid target code, so the function is total without creating spurious positive instances. This isolates the finite coding and computability work from the generic transfer of many-one hardness and undecidability.
--
--   **Formalization Note** Invalid codes are negative instances by definition. A fixed code with dimension zero is a convenient fixed invalid target; this is equivalent to the paper's choice of a fixed non-GAS, non-Lyapunov-stable field for the discarded inputs.
-- source:
--   Shevchenko, Liu, Liu (2026), arXiv:2610.12434 (SHA-256 72e185f4750fe9bb72a2f146b2802fa13a97dcdd4f66e0e762b703dc7ddd77a8), proof of Theorem 2.1, printed p. 35 (PDF 37), using Theorem 2.4 (printed pp. 5–6) and Lemma 6.1 (printed p. 35).

import Definitions.Def_HGASUndecidable_Main_Codes

open Filter Topology MeasureTheory
open scoped BigOperators

theorem HGASUndecidable.Main.theorem_2_1_code_reduction (n₀ k₀ n j : ℕ) (hn₀ : 1 ≤ n₀) (hk₀ : 1 ≤ k₀)
    (hn : Nat.choose (n₀+k₀-1) k₀ ≤ n) :
    ∃ r : ℕ → ℕ, Computable r ∧
      (∀ e : ℕ, HGASUndecidable.Main.HGAS n₀ (2*k₀+1) e ↔ HGASUndecidable.Main.HGAS n (3+2*j) (r e)) ∧
      (∀ e : ℕ, HGASUndecidable.Main.HLS n₀ (2*k₀+1) e ↔ HGASUndecidable.Main.HLS n (3+2*j) (r e)) := by sorry
