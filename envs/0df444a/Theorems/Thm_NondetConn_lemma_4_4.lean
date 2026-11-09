-- Prove2me | Theorems.Thm_NondetConn_lemma_4_4
-- name    : NondetConn.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:27:06.393487+00:00
-- url     : https://prove2.me/theorems/41c1bc07-a9a6-4e09-8718-75edf3445845
-- title:
--   Lemma 4.4 — shortcutting $(u, a(u))$ keeps $\hat b^{-1}\hat a$ a single $(n-1)$-cycle
-- statement:
--   Let $N = 2n$ and let $\mathcal A \times \mathcal B$ be a 1-monochromatic rectangle of $\mathsf{bConn}_N$, i.e. $\mathsf{bConn}_N(a,b) = 1$ for all $a \in \mathcal A$, $b \in \mathcal B$. Fix $u \in [n]$. For every $a \in \mathcal A$ and $b \in \mathcal B$, with $v = a(u)$, $\hat a = a_{(u,v)}$ and $\hat b = b_{(u,v)}$,
--   $$
--   \hat b^{-1}\hat a \ \text{ consists of a single } (n-1)\text{-cycle on } [n]\setminus\{u\}.
--   $$
--   Equivalently, for all $u, v$ with $a(u) = v$ for some $a \in \mathcal A$, every pair in $\mathcal A_{(u,v)} \times \mathcal B_{(u,v)}$ is a 1-input of $\mathsf{bConn}_{N-2}$ after renaming $[n]\setminus\{u\}$ and $[n]\setminus\{v\}$ to $[n-1]$.
--
--   This is what lets the recurrence of Lemma 4.3 pass from $S_n$ to $S_{n-1}$.
--
--   Differences from the source:
--   - generalization: 𝒜 × ℬ is the maximizer in the definition of S_n with |𝒜| ≥ |ℬ| (§4.1, p.10) → 𝒜 × ℬ is any 1-monochromatic rectangle of bConn_N (∀ a ∈ 𝒜, ∀ b ∈ ℬ, bConn n a b); reason: the proof uses only 𝒜 × ℬ ⊆ bConn_N⁻¹(1) (footnote 13, p.19); the maximizer is such a rectangle
--   - generalization: n > 1 (the setting of Lemma 4.3, whose proof §4.1 is) → every n; reason: for n ≤ 1 the statement is immediate (no u or an empty [n]∖{u}); it specializes to n > 1
--   - encoding: for all (â, b̂) ∈ 𝒜_(u,v) × ℬ_(u,v), for u, v with a(u) = v for some a ∈ 𝒜 → for all a ∈ 𝒜 and b ∈ ℬ, with v := a u, conn (restrictAt a u) (shortcut b u (a u)); reason: the same quantification written through the members a, b; "single (n−1)-cycle on [n]∖{u}" is conn on {x // x ≠ u}
--   - encoding: [n], b⁻¹a, n = N/2 → Fin n (0-based), b⁻¹ * a (apply a first), bConn n; reason: Lean conventions; same instances
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), Lemma 4.4, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_NondetConn_bConn
import Definitions.Def_NondetConn_restrictAt
import Definitions.Def_NondetConn_shortcut

namespace NondetConn

/-- **Lemma 4.4** (Zhang, *Settling Nondeterministic Communication Complexity of Graph Connectivity*, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), §4.1, p.10).
Let `𝒜 × ℬ` be a 1-monochromatic rectangle of `bConn_N` (`N = 2n`). For every `u ∈ [n]`,
every `a ∈ 𝒜` and every `b ∈ ℬ`, with `v = a(u)`, the permutation `b̂⁻¹â` of `[n] \ {u}`,
where `â = a_(u,v)` and `b̂ = b_(u,v)`, consists of a single `(n − 1)`-cycle on `[n] \ {u}`.

**Formalization Note** Stated for every 1-monochromatic rectangle, not only the maximizer of
`S_n` with `|𝒜| ≥ |ℬ|` (the proof uses only `𝒜 × ℬ ⊆ bConn⁻¹(1)`). Quantifying over `a ∈ 𝒜`
with `v = a u` and `b ∈ ℬ` is quantifying over `(â, b̂) ∈ 𝒜_(u,v) × ℬ_(u,v)`. -/
theorem lemma_4_4 (n : ℕ) (𝒜 ℬ : Finset (Equiv.Perm (Fin n)))
    (hrect : ∀ a ∈ 𝒜, ∀ b ∈ ℬ, bConn n a b) (u : Fin n) :
    ∀ a ∈ 𝒜, ∀ b ∈ ℬ, conn (restrictAt a u) (shortcut b u (a u)) := by sorry

end NondetConn
