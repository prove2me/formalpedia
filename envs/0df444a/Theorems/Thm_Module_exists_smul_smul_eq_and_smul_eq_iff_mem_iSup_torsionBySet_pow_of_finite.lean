-- Prove2me | Theorems.Thm_Module_exists_smul_smul_eq_and_smul_eq_iff_mem_iSup_torsionBySet_pow_of_finite
-- name    : Module.exists_smul_smul_eq_and_smul_eq_iff_mem_iSup_torsionBySet_pow_of_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/b94f5e80-0df9-56b2-a4d4-863b7f6bbd3a
-- title:
--   Idempotent element projecting a finite submodule onto its P-primary part
-- statement:
--   Let $T$ be a commutative ring, let $M$ be an abelian group carrying a $T$-module structure, let $N$ be a $T$-submodule of $M$ whose underlying type is finite, and let $\mathfrak P$ be an arbitrary ideal of $T$ (no maximality or primality is assumed). The assertion is that there exists an element $t \in T$ with the following two properties. First, $t$ acts idempotently on $N$: for every $x \in N$ one has $t \cdot (t \cdot x) = t \cdot x$. Second, the fixed points of $t$ on $N$ are exactly the $\mathfrak P$-power torsion elements: for every $x \in N$, the equality $t \cdot x = x$ holds if and only if $x$ belongs to $\bigsqcup_{k \in \mathbb{N}} \{y \in M : a \cdot y = 0 \text{ for all } a \in \mathfrak P^k\}$, the supremum over all natural numbers $k$ of the $\mathfrak P^k$-torsion submodules of $M$ (membership being tested in $M$, not merely in $N$). Thus multiplication by $t$ is an idempotent projector of $N$ onto $N \cap M[\mathfrak P^\infty]$.
--
--   This is the construction of the primary idempotent at $\mathfrak P$ for a finite module over a commutative ring: a single ring element whose action on $N$ is an idempotent projector with image the $\mathfrak P$-primary part. It is used in the Hecke-algebra setting, where it yields the analogous projector onto the Eisenstein-primary torsion in a tower of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_exists_smul_smul_eq_and_smul_eq_iff_mem_iSup_torsionBySet_pow_of_finite.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Module.exists_smul_smul_eq_and_smul_eq_iff_mem_iSup_torsionBySet_pow_of_finite
    {T : Type*} [CommRing T] {M : Type*} [AddCommGroup M] [Module T M]
    (N : Submodule T M) [Finite ↥N] (𝔓 : Ideal T) :
    ∃ t : T, (∀ x ∈ N, t • (t • x) = t • x) ∧
      ∀ x ∈ N, (t • x = x ↔ x ∈ ⨆ k : ℕ, Submodule.torsionBySet T M (↑(𝔓 ^ k) : Set T)) := by sorry
