-- Prove2me | Theorems.Thm_LosslessCond_Supplement_theorem_A_1
-- name    : LosslessCond.Supplement.theorem_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:25:26.597834+00:00
-- url     : https://prove2.me/theorems/f6316b9b-9bea-431f-9ed1-be4358c24153
-- title:
--   Theorem A.1 — local-to-global principle; if all $2^{4s}$-bounded submatrices have depth $\le s$, then $D(M)\le 3s-2$
-- statement:
--   Let $M:X\times Y\to\{0,1\}$ be a finite total Boolean matrix and write $D(\cdot)$ for deterministic two-party communication complexity, where a submatrix $M[U,V]$ consists of original rows $U\subseteq X$ and original columns $V\subseteq Y$. Let $s\ge1$ be an integer. If every nonempty submatrix $M[U,V]$ with $|U|\le 2^{4s}$ and $|V|\le 2^{4s}$ satisfies $D(M[U,V])\le s$, then
--
--   $$
--   D(M)\le 3s-2 .
--   $$
--
--   Equivalently, if $D(M)>3s-2$, some submatrix within those size bounds has depth at least $s+1$.
--
--   The hypothesis bounds the sizes from above only: a matrix with fewer rows or columns tests its existing restrictions. The theorem says that the hardness of a matrix is always witnessed by a submatrix whose size is exponential in that hardness, at the price of a factor of about $3$.
--
--   **Formalization Note** Submatrices are given by `Finset`s of original labels, $D(M[U,V])$ is `DetCCHard.commCost M U V` and $D(M)$ is `DetCCHard.Dcost M`; `3 * s - 2` is exact in $\mathbb N$ since $s\ge1$.
--
--   Differences from the source:
--   - encoding: submatrix $M[U,V]$ on nonempty sets of original labels → nonempty `Finset`s `U`, `V` with cost `DetCCHard.commCost M U V` (least depth of a protocol correct on $U\times V$); reason: Lean convention of the base mission, the same cost as the submatrix's own complexity
--   - encoding: $3s-2$ → `3 * s - 2` in ℕ (truncated subtraction); reason: exact since $s\ge1$, so no instance changes
-- source:
--   Mackenzie, Lossless Hardness Condensation in Deterministic Communication Complexity, arXiv:2609.28691 (held version, sha256 ce75e6d41cda6fdcdc55c619ab80e2b628e40845768cc3021cc0a0bfe7743fcf), Theorem A.1, p.23 (PDF p.24)

import Mathlib
import Definitions.Def_DetCCHard_commCost

namespace LosslessCond

namespace Supplement

/-- **Theorem A.1 (Local-to-global principle)** (Mackenzie, *Lossless Hardness Condensation in
Deterministic Communication Complexity*, arXiv:2609.28691, held version sha256 ce75e6d4…, p.23,
PDF p.24). Let `s ≥ 1` be an integer. If every nonempty submatrix of `M` with at most `2^{4s}` rows
and at most `2^{4s}` columns has depth at most `s`, then `D(M) ≤ 3s − 2`.

**Formalization Note** `M : X → Y → Bool` on finite types is a finite total Boolean matrix; no
`Nonempty` hypothesis (an empty side gives `D(M) = 0`). A submatrix is given by `Finset`s `U`, `V`
of distinct original labels, its depth is `DetCCHard.commCost M U V` (least depth of a protocol
correct on `U × V`), and `D(M)` is `DetCCHard.Dcost M`. "At most" sizes: `U.card ≤ 2^(4s)`,
`V.card ≤ 2^(4s)`. `3 * s - 2` is natural subtraction, exact since `s ≥ 1`. The paper's
"Equivalently" sentence is the contrapositive of this implication. -/
theorem theorem_A_1 {X Y : Type} [Fintype X] [Fintype Y] (M : X → Y → Bool) (s : ℕ) (hs : 1 ≤ s)
    (hloc : ∀ (U : Finset X) (V : Finset Y), U.Nonempty → V.Nonempty →
      U.card ≤ 2 ^ (4 * s) → V.card ≤ 2 ^ (4 * s) →
      DetCCHard.commCost M (U : Set X) (V : Set Y) ≤ s) :
    DetCCHard.Dcost M ≤ 3 * s - 2 := by sorry

end Supplement

end LosslessCond
