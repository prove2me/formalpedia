-- Prove2me | Theorems.Thm_IncrementalER_Supplement_theorem_4_1
-- name    : IncrementalER.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:52:12.498925+00:00
-- url     : https://prove2.me/theorems/4dccffd9-b9a4-4947-8cdb-cdae197a742b
-- title:
--   Theorem 4.1 — terminal-robust initialization and decoupled batch insertion
-- statement:
--   For every connected positive-capacity graph with quasipolynomial capacity ratio and every real $k>1$, uniform randomized exact-real-RAM programs initialize a $k$-hitting set $T$ of size $\widetilde O(m/k)$ satisfying $\mathbb E[f_T(v)]=O(1)$ for every vertex.
--
--   For any one batch $B$, a decoupled `InsertVertices(B)` call returns $D$ with $B\subseteq D$, $|D|\le2|B|$, and $\mathbb E[f_{T\cup D}(v)]=O(1)$ for every vertex. Initialization costs $\widetilde O(m\operatorname{poly}(k))$, one call costs $\widetilde O(|B|\operatorname{poly}(k))$, and correctness holds with high probability. Outputs from separate calls are not accumulated.
--
--   Differences from the source:
--   - encoding: informal randomized data structure and O-tilde work → separate admissible initialization and batch programs on PNormReg, with every call restarted from the same initialized memory and all work charged; reason: this is the literal decoupled-call semantics emphasized immediately after Theorem 4.1
--   - encoding: expectations of nonnegative insertion costs → lower integrals of ENNReal.ofReal over the fair-coin tape; reason: this avoids the zero value of a non-integrable Bochner integral and preserves the finite expectations asserted by the source
--   - generalization: graph edges join distinct vertices → edge-list inputs may also contain loops, ignored by all graph quantities; reason: removing loops preserves the source instance and only decreases the size parameter used in upper bounds
-- source:
--   Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, Incremental All-Pairs Effective Resistance in Almost-Linear Time, STOC 2027 submission (manuscript sha256 a0415fd5…), Theorem 4.1, p.15

import Mathlib
import Definitions.Def_IncrementalER_Supplement_theorem41Spec

set_option autoImplicit false

namespace IncrementalER.Supplement

/-- **Theorem 4.1** (Goranci et al., STOC 2027 submission, manuscript sha256 a0415fd5…, p.15).
There are uniform initialization and batch programs satisfying the full `k`-hitting-set,
`E[f_T(v)]=O(1)`, decoupled `InsertVertices(B)`, factor-two size, time and high-probability clauses
of the printed theorem. -/
theorem theorem_4_1 :
    ∀ A : ℝ, 0 < A → ∀ q : ℕ, ∀ c : ℝ, 1 < c →
      ∃ Pre Batch : PNormReg.Program, ∃ C : ℝ, ∃ r p : ℕ,
        A ≤ C ∧ q ≤ r ∧ theorem41Spec Pre Batch C r p c := by sorry

end IncrementalER.Supplement
