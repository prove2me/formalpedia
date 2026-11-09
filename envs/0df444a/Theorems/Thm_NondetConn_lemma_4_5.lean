-- Prove2me | Theorems.Thm_NondetConn_lemma_4_5
-- name    : NondetConn.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:27:34.040364+00:00
-- url     : https://prove2.me/theorems/1ee105d7-5ee9-41f6-9e0f-7f596a3bb5b7
-- title:
--   Lemma 4.5 — multiplicity of $b_{(u,v)}$ is at most $|\mathcal W_{(u,b^{-1}(v))}(b)| + 1$
-- statement:
--   Let $N = 2n$ and let $\mathcal A \times \mathcal B$ be a 1-monochromatic rectangle of $\mathsf{bConn}_N$. For any $u, v \in [n]$ such that $a(u) = v$ for some $a \in \mathcal A$, and any $b \in \mathcal B$,
--   $$
--   \bigl|\{b' \in \mathcal B \mid b'_{(u,v)} = b_{(u,v)}\}\bigr| \le \bigl|\mathcal W_{(u,\,b^{-1}(v))}(b)\bigr| + 1 ,
--   $$
--   where $\mathcal W$ is taken with respect to $\mathcal A$.
--
--   It bounds how many members of $\mathcal B$ collapse to the same shortcut map, which is the remaining entropy term in the proof of Lemma 4.3.
--
--   Differences from the source:
--   - generalization: 𝒜 × ℬ is the maximizer in the definition of S_n with |𝒜| ≥ |ℬ| (§4.1, p.10) → 𝒜 × ℬ is any 1-monochromatic rectangle of bConn_N (∀ a ∈ 𝒜, ∀ b ∈ ℬ, bConn n a b); reason: the proof uses only 𝒜 × ℬ ⊆ bConn_N⁻¹(1) (footnote 13, p.19); the maximizer is such a rectangle
--   - generalization: n > 1 (the setting of Lemma 4.3, whose proof §4.1 is) → every n; reason: for n ≤ 1 the statement is immediate (no u or an empty [n]∖{u}); it specializes to n > 1
--   - encoding: b′_(u,v) = b_(u,v); 𝒲_(u,b⁻¹(v))(b) with 𝒜 implicit → equality of the bijections shortcut b′ u v = shortcut b u v on {x // x ≠ u}; W 𝒜 b u (b⁻¹ v); reason: maps on [n]∖{u} are equal iff they agree on every x ≠ u; 𝒲 depends on 𝒜, made explicit
--   - encoding: [n], b⁻¹a, n = N/2 → Fin n (0-based), b⁻¹ * a (apply a first), bConn n; reason: Lean conventions; same instances
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), Lemma 4.5, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_NondetConn_bConn
import Definitions.Def_NondetConn_shortcut
import Definitions.Def_NondetConn_W

namespace NondetConn

/-- **Lemma 4.5** (Zhang, *Settling Nondeterministic Communication Complexity of Graph Connectivity*, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), §4.1, p.11).
Let `𝒜 × ℬ` be a 1-monochromatic rectangle of `bConn_N` (`N = 2n`). For any `u, v ∈ [n]` such
that `a(u) = v` for some `a ∈ 𝒜`, and any `b ∈ ℬ`,
`|{b′ ∈ ℬ | b′_(u,v) = b_(u,v)}| ≤ |𝒲_(u, b⁻¹(v))(b)| + 1`.

**Formalization Note** Stated for every 1-monochromatic rectangle (not only the maximizer of
`S_n`). `b′_(u,v) = b_(u,v)` is equality of the shortcut maps on `[n] \ {u}`; `𝒲` is `W 𝒜`
(it depends on `𝒜`). -/
theorem lemma_4_5 (n : ℕ) (𝒜 ℬ : Finset (Equiv.Perm (Fin n)))
    (hrect : ∀ a ∈ 𝒜, ∀ b ∈ ℬ, bConn n a b) (u v : Fin n) (huv : ∃ a ∈ 𝒜, a u = v)
    (b : Equiv.Perm (Fin n)) (hb : b ∈ ℬ) :
    (ℬ.filter (fun b' => shortcut b' u v = shortcut b u v)).card ≤ (W 𝒜 b u (b⁻¹ v)).card + 1 := by sorry

end NondetConn
