-- Prove2me | Theorems.Thm_HiddenPartition_luw95_high_girth
-- name    : HiddenPartition.luw95_high_girth
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:27:45.347053+00:00
-- url     : https://prove2.me/theorems/65b59584-9355-4071-a542-e2710006b435
-- title:
--   [LUW95, Thm 3.2] as used in Lemma 3.2: $q$-regular bipartite graphs of girth $\ge\ell+5$ with $\le q^{\ell-\lfloor(\ell+2)/4\rfloor+1}$ vertices per side
-- statement:
--   This is the high-girth construction of Lazebnik, Ustimenko and Woldar, in the form in which the proof of Lemma 3.2 uses it.
--
--   Let $q$ be a prime power and let $\ell\ge3$ be odd. There is a simple $q$-regular bipartite graph $J=(A,B,E)$ with $|A|=|B|=M$ whose girth is at least $\ell+5$ and which has at most
--
--   $$q^{\,\ell-\lfloor(\ell+2)/4\rfloor+1}$$
--
--   vertices on each side.
--
--   The proof of Lemma 3.2 applies it with $q=p$ a power of two in $[n,2n)$ and $\ell=2t-3$, where $\ell+5=2(t+1)$ and $\ell-\lfloor(\ell+2)/4\rfloor+1=\lceil3(t-1)/2\rceil$; it is the source of the size bound $(2n)^{\lceil3(t-1)/2\rceil}$.
--
--   **Formalization Note** The exponent is computed in natural numbers; $\lfloor(\ell+2)/4\rfloor\le\ell$, so no truncation occurs.
--
--   Differences from the source:
--   - generalization: p a power of two (n ≤ p < 2n), ℓ = 2t − 3 with t ≥ 3 → every prime power q and every odd ℓ ≥ 3; reason: LUW95's hypothesis is a prime power and any odd ℓ; every power of two is a prime power and ℓ = 2t − 3 is odd and ≥ 3 for t ≥ 3, so the Lean statement specializes to the cited use
--   - encoding: a simple bipartite graph J = (A, B, E) with |A| = |B| = M (A, B nonempty, §3.1) → bip R for a biadjacency matrix R : Fin M → Fin M → Bool with 0 < M; reason: every simple bipartite graph with fixed nonempty sides of size M is bip R for a unique R; same instances (0 < M excludes the empty graph, which is vacuously regular)
--   - encoding: girth (infinite for a forest) → Mathlib extended girth egirth : ℕ∞; reason: same value; ⊤ for a forest as on p.9
-- source:
--   H. Agrawal, P. Eua-anant, B. Haeupler, B. Laekhanukit, P. Mihov, L. Milenković, R. Santos, Z. Zhang, From One Hidden Subgraph to Dense Graph Partitions with Applications to Hardness of Clustering, STOC 2027 submission (manuscript sha256 17239d0bf911912040cb82c45ae979b179c419fb0b9e69d6d1413bf70068b601), proof of Lemma 3.2, p.14 (pdf p.16), citing [LUW95, Theorem 3.2] (F. Lazebnik, V. A. Ustimenko, A. J. Woldar, A new series of dense graphs of high girth, Bull. AMS 32 (1995), https://doi.org/10.1090/S0273-0979-1995-00569-0)

import Mathlib
import Definitions.Def_HiddenPartition_bip

set_option autoImplicit false

open Classical

namespace HiddenPartition

/-- **[LUW95, Theorem 3.2], as used in the proof of Lemma 3.2** (Agrawal, Eua-anant, Haeupler, Laekhanukit, Mihov, Milenković, Santos, Zhang,
*From One Hidden Subgraph to Dense Graph Partitions with Applications to Hardness of Clustering*, STOC 2027
submission (manuscript sha256 17239d0b…),
p.14 (pdf p.16)).

For every prime power `q` and every odd `ℓ ≥ 3` there is a simple `q`-regular bipartite graph
`J = (A, B, E)` with `|A| = |B| = M`, girth at least `ℓ + 5`, and at most
`q^{ℓ - ⌊(ℓ+2)/4⌋ + 1}` vertices on each side.

**Formalization Note.** `J` is `bip R` for a biadjacency matrix `R : Fin M → Fin M → Bool`
(sides `inl`, `inr`); the sides are non-empty (`0 < M`), as for every graph `J = (A, B, E)`
of §3.1 ("`A` and `B` finite nonempty sets"), so that `q`-regularity is not vacuous. Girth is Mathlib's extended girth `egirth` (`⊤` for a forest). The
exponent `ℓ - (ℓ + 2) / 4 + 1` is computed in `ℕ`; `(ℓ + 2) / 4 ≤ ℓ`, so the subtraction
does not truncate, and `/` is the floor. The paper applies it with `q = p` a power of two and
`ℓ = 2t - 3`, `t ≥ 3`. -/
theorem luw95_high_girth (q : ℕ) (hq : IsPrimePow q) (ℓ : ℕ) (hℓodd : Odd ℓ) (hℓ : 3 ≤ ℓ) :
    ∃ (M : ℕ) (R : Fin M → Fin M → Bool),
      0 < M ∧
      (bip R).IsRegularOfDegree q ∧
      ((ℓ + 5 : ℕ) : ℕ∞) ≤ (bip R).egirth ∧
      M ≤ q ^ (ℓ - (ℓ + 2) / 4 + 1) := by sorry

end HiddenPartition
