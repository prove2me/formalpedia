-- Prove2me | Theorems.Thm_MMSDelta2_proposition_5_3
-- name    : MMSDelta2.proposition_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:57:40.193378+00:00
-- url     : https://prove2.me/theorems/e0926675-a05c-4515-866a-c406314c6cb3
-- title:
--   Proposition 5.3 — the integer KPW core $A=2^{750}M$
-- statement:
--   Let $A=\alpha M$ with $\alpha=2^{750}$, a nonnegative integer matrix. Then:
--
--   1. $A$ has exactly $19$ positive entries;
--   2. every row and every column of $A$ sums to $\alpha$;
--   3. $\alpha$ and every entry of $A$ have at most $751$ bits;
--   4. if $(X_1,\dots,X_5)$ is a partition of $A^+=\{(i,j):A_{i,j}>0\}$ with $\sum_{(i,j)\in X_t}A_{i,j}\ge\alpha$ for every $t\in[5]$, then $(X_1,\dots,X_5)$ is the row partition or the column partition, up to relabeling.
--
--   This summarizes the properties of the core used by the reductions of §§6–7.
--
--   **Formalization Note** "At most $751$ bits" is `Nat.size ≤ 751`.
--
--   Differences from the source:
--   - generalization: there exist a nonnegative integer matrix A and α = 2^750 with properties 1–4 → properties 1–4 for the matrix A = 2^750·M constructed in §5.1; reason: naming the witness implies the existential statement; §7 uses this A ('the 5 × 5 KPW integer matrix A given by Proposition 5.3')
--   - encoding: partitions, relabeling, bit length → indexed families of pairwise disjoint sets with union A⁺; permutations; Nat.size; reason: same statement
-- source:
--   Gupta, Seetharaman, The Existence of Maximin Share Allocations is Δ₂ᴾ-complete, arXiv:2609.15841 (held version, sha256 a43b06b9…), Proposition 5.3, pp.20–21 (PDF pp.22–23)

import Mathlib
import Definitions.Def_MMSDelta2_KPW

namespace MMSDelta2

/-- **Proposition 5.3**, pp.20–21 (PDF pp.22–23).

S. Gupta, S. Seetharaman, *The Existence of Maximin Share Allocations is Δ₂ᴾ-complete*,
arXiv:2609.15841 (held version, sha256 a43b06b9…).

The nonnegative integer matrix `A = αM` and `α = 2^750` satisfy: (1) `A` has exactly 19 positive
entries; (2) every row and every column of `A` sums to `α`; (3) `α` and every entry of `A` have at
most 751 bits; (4) if `(X_1, …, X_5)` is a partition of `A⁺` with `Σ_{(i,j)∈X_t} A_{i,j} ≥ α` for every
`t ∈ [5]`, then it is the row partition or the column partition, up to relabeling.

**Formalization Note.** The paper states "There exist a nonnegative integer matrix `A` and a
positive integer `α = 2^750`" with (1)–(4); this item states (1)–(4) for the matrix the paper
constructs, `kpwA = 2^750·M` (natural-number entries), which implies the existential statement.
"At most 751 bits" is `Nat.size ≤ 751`. -/
theorem proposition_5_3 :
    kpwAplus.card = 19 ∧
    (∀ i, ∑ j, kpwA i j = kpwAlpha) ∧ (∀ j, ∑ i, kpwA i j = kpwAlpha) ∧
    (Nat.size kpwAlpha ≤ 751 ∧ ∀ i j, Nat.size (kpwA i j) ≤ 751) ∧
    (∀ X : Fin 5 → Finset (Fin 5 × Fin 5), IsPartitionOf kpwAplus X →
      (∀ t, kpwAlpha ≤ ∑ p ∈ X t, kpwA p.1 p.2) → IsRowOrColPartition kpwAplus X) := by sorry

end MMSDelta2
