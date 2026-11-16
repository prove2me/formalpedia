-- Prove2me | Theorems.Thm_GeoQAC_Supplement_theorem_4_4
-- name    : GeoQAC.Supplement.theorem_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:27:18.928235+00:00
-- url     : https://prove2.me/theorems/1a6e194a-c163-4cce-8e3a-e548ba5ce807
-- title:
--   Theorem 4.4 — exact clean MAJORITY and MOD at depth $O(d)$ and width $n^{O(1/d)}$
-- statement:
--   1. There is a constant $C_0>0$ such that for every depth parameter $d\ge1$ there is $N$ with: for every $n\ge N$ there is an exact clean implementation of $U_{\mathrm{MAJ}_n}$ by a $[w,h]$-2D-QAC circuit of depth at most $C_0d$ and width
--   $$
--   w\le n^{C_0/d},
--   $$
--   with any number of ancillas.
--   2. For every fixed modulus $r\ge2$ the same holds for $U_{\mathrm{MOD}_{r,n}}$, with a constant $C_0$ depending on $r$.
--
--   Together with the lower bounds of Theorems 3.18 and 3.19 this gives width $n^{\Theta(1/d)}$ for MAJORITY and MOD at large fixed depths.
--
--   Differences from the source:
--   - encoding: exact clean synthesis with unrestricted product ancillas → published GeoQAC.IsCleanImpl: ancillas |0⟩ in and out, one global phase, logical qubits anywhere; reason: a product ancilla state is prepared and restored by one-qubit gates in L_0 and L_d (p.38), which change no depth or layout
--   - reading: for every fixed d, depth O(d) and width n^{O(1/d)} → one C₀ (chosen before d) in depth ≤ C₀ d and width ≤ n^{C₀/d}, for n ≥ N(d); C₀ may depend on the fixed modulus r for MOD; reason: the proof states "an exponent constant independent of d" (p.32); asymptotic notation in n for fixed d
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), Theorem 4.4, p.32

import Mathlib
import Definitions.Def_GeoQAC_QACCircuit_Is2D
import Definitions.Def_GeoQAC_IsCleanImpl
import Definitions.Def_GeoQAC_Supplement_hammingWeight

namespace GeoQAC.Supplement

open GeoQAC

/-- **Theorem 4.4** (Dong, Ou, Yao, arXiv:2604.07178, version of 2026-11-03, p.32). "For every fixed
`d ≥ 1`, the MAJORITY and fixed-modulus MOD unitaries admit exact clean depth-`O(d)` 2D-QAC
synthesis with unrestricted product ancillas and width `n^{O(1/d)}`."

**Formalization Note.**
* The constant `C₀` in `depth ≤ C₀·d` and `width ≤ n^{C₀/d}` is chosen before `d` (proof, p.32:
  "with an exponent constant independent of d"); the threshold `N` may depend on the fixed `d`.
  For MOD, `C₀` may depend on the fixed modulus `r ≥ 2`.
* Exact clean implementation of `U_f` is the published `GeoQAC.IsCleanImpl` with ancillas `|0⟩` in
  and out (a product ancilla state is converted to `|0^a⟩` and back by one-qubit gates, p.38); the
  length `h` (the number of ancillas) is unrestricted. -/
theorem theorem_4_4 :
    (∃ C₀ : ℝ, 0 < C₀ ∧ ∀ d : ℕ, 1 ≤ d → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ (w h D : ℕ) (C : QACCircuit (Pos w h) D) (ctrl : Fin n ↪ Pos w h) (acc : Pos w h),
        C.Is2D ∧ (D : ℝ) ≤ C₀ * d ∧ (w : ℝ) ≤ (n : ℝ) ^ (C₀ / d) ∧
        IsCleanImpl C ctrl acc (majFn n)) ∧
    (∀ r : ℕ, 2 ≤ r → ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ d : ℕ, 1 ≤ d → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ (w h D : ℕ) (C : QACCircuit (Pos w h) D) (ctrl : Fin n ↪ Pos w h) (acc : Pos w h),
        C.Is2D ∧ (D : ℝ) ≤ C₀ * d ∧ (w : ℝ) ≤ (n : ℝ) ^ (C₀ / d) ∧
        IsCleanImpl C ctrl acc (modFn r n)) := by sorry

end GeoQAC.Supplement
