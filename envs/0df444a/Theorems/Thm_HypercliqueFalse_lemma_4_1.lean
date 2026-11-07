-- Prove2me | Theorems.Thm_HypercliqueFalse_lemma_4_1
-- name    : HypercliqueFalse.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:32:22.430275+00:00
-- url     : https://prove2.me/theorems/ce5cdfab-2e4f-438c-b159-967137fc4263
-- title:
--   Lemma 4.1 (Recursive Step) — the identities and sizes of both reductions
-- statement:
--   Let $h \ge 3$ and $q \in \mathbb N$.
--
--   1. **First reduction.** For arrays $A, B, C, D, E$ of $T_h$ of size $(N, M, a, b, c)$ with $N = N'q$, let $(\bar A^g,\dots,\bar E^g)$ ($g \in [q]$) be the main children of size $(N/q, M, qa, b, c)$ and $(\bar A^{ij},\dots,\bar E^{ij})$ ($i, j\in[q]$) the correction children of size $(N/q, M, a, b, 2c)$ constructed in the proof (`firstMain`, `firstCorr`). Then
--   $$
--   T_h(A,B,C,D,E) = \sum_{g\in[q]} T_h(\bar A^g,\bar B^g,\bar C^g,\bar D^g,\bar E^g) + \sum_{1\le i<j\le q} T_h(\bar A^{ij},\bar B^{ij},\bar C^{ij},\bar D^{ij},\bar E^{ij}).
--   $$
--   2. **Second reduction.** For arrays of size $(N, M, a, b, c)$ with $M = M'q$, the same identity holds with the children of the second reduction (`secondMain`, `secondCorr`), of sizes $(N, M/q, a, qb, c)$ and $(N, M/q, a, b, 2c)$.
--
--   Applied recursively, alternating between the two reductions, this rewrites $H_h$ as a sum of instances of $T_h$ with $N = M = \sqrt n$, which Lemma 4.3 evaluates. The companion item `lemma_4_1_linear_time` states that the children are computed in linear time.
--
--   **Formalization Note** The sizes are part of the children's types.
--
--   Differences from the source:
--   - encoding: children of size (N/q, M, …) and (N, M/q, …) → N = N'·q (resp. M = M'·q), children typed with N' (resp. M'); reason: the paper's N/q presupposes q | N ("N and M are powers of some integer constant q", p.10)
--   - encoding: "we identify [q] × [a] with [qa]" and "[2] × [c] with [2c]" → finProdFinEquiv, (j, α) ↦ a·j + α and (t, γ) ↦ c·t + γ, 0-based; reason: a fixed identification as in the paper; same polynomials
--   - reading: "we can compute … new arrays … such that" the identity holds → the identity for the explicit arrays of the proof; reason: an existential over arrays of the given sizes would be trivial (put the value into one entry); the lemma's content is the proof's arrays, whose construction is linear-time
--   - reading: second reduction: "analogous: we split x₁ and x₄ instead … move it into the dimension b … The correction terms are handled as before" (no formulas) → the explicit arrays secondMain, secondCorr; reason: the arrays the description determines via Lemma 3.1; both identities were checked on concrete integer instances
--   - generalization: q an integer constant (q ≥ 2 in the recursion) → every q : ℕ; reason: the identities hold for every q (q = 1: one main child, no corrections); specializes to the paper's q
-- source:
--   Fischer, The Hyperclique Hypothesis is False, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Lemma 4.1, p.10; proof, pp.10–11

import Mathlib
import Definitions.Def_HypercliqueFalse_tPoly
import Definitions.Def_HypercliqueFalse_firstMain
import Definitions.Def_HypercliqueFalse_firstCorr
import Definitions.Def_HypercliqueFalse_secondMain
import Definitions.Def_HypercliqueFalse_secondCorr

set_option autoImplicit false

namespace HypercliqueFalse

/-- **Lemma 4.1 (Recursive Step), the identities and the sizes.** Fischer, *The Hyperclique Hypothesis is False*, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Lemma 4.1, p.10:
"T_h(A, B, C, D, E) = Σ_{g∈[q]} T_h(Ā^g, B̄^g, C̄^g, D̄^g, Ē^g) + Σ_{1≤i<j≤q} T_h(Ā^{ij}, B̄^{ij}, C̄^{ij},
D̄^{ij}, Ē^{ij}). Here, the polynomials in the first sum have size (N/q, M, qa, b, c) and those in the
second sum have size (N/q, M, a, b, 2c). Alternatively, we can achieve sizes (N, M/q, a, qb, c) and
(N, M/q, a, b, 2c) instead."

Both reductions, with the explicit children of the proof (pp.10–11; `firstMain`, `firstCorr`,
`secondMain`, `secondCorr`); the sizes are the children's types. The linear-time clause is
`lemma_4_1_linear_time`.

**Formalization Note.** `N = N'·q` (resp. `M = M'·q`) for the paper's "N/q" (resp. "M/q"); Section 4
has `h ≥ 3`; the identities are stated for every `q`. -/
theorem lemma_4_1 (h q : ℕ) (hh : 3 ≤ h) :
    (∀ (N' M a b c n : ℕ) (T : TData h (N' * q) M a b c n),
      tPoly T = ∑ g, tPoly (firstMain T g) + ∑ i, ∑ j ∈ Finset.Ioi i, tPoly (firstCorr T i j)) ∧
    (∀ (N M' a b c n : ℕ) (T : TData h N (M' * q) a b c n),
      tPoly T = ∑ g, tPoly (secondMain T g) + ∑ i, ∑ j ∈ Finset.Ioi i, tPoly (secondCorr T i j)) := by sorry

end HypercliqueFalse
