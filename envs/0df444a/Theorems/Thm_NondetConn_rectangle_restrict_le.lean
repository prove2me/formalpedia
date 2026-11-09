-- Prove2me | Theorems.Thm_NondetConn_rectangle_restrict_le
-- name    : NondetConn.rectangle_restrict_le
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:31:04.474511+00:00
-- url     : https://prove2.me/theorems/37826578-42c3-4141-9104-d4915f46f87c
-- title:
--   Proof of Lemma 4.3 — $\log|\mathcal A_{(u,v)}\times\mathcal B_{(u,v)}| \le S_{n-1}$
-- statement:
--   Let $N = 2n$, let $\mathcal A \times \mathcal B$ be a 1-monochromatic rectangle of $\mathsf{bConn}_N$, and let $u, v \in [n]$ with $a(u) = v$ for some $a \in \mathcal A$. Then
--   $$
--   \log_2 \bigl|\mathcal A_{(u,v)} \times \mathcal B_{(u,v)}\bigr| \le S_{n-1}.
--   $$
--
--   This is the source of the $S_{n-1}$ term in the recurrence of Lemma 4.3: by Lemma 4.4, $\mathcal A_{(u,v)} \times \mathcal B_{(u,v)}$ is a 1-monochromatic rectangle for $n - 1$ after renaming.
--
--   Differences from the source:
--   - generalization: 𝒜 × ℬ is the maximizer in the definition of S_n with |𝒜| ≥ |ℬ| (§4.1, p.10) → 𝒜 × ℬ is any 1-monochromatic rectangle of bConn_N (∀ a ∈ 𝒜, ∀ b ∈ ℬ, bConn n a b); reason: the proof uses only 𝒜 × ℬ ⊆ bConn_N⁻¹(1) (footnote 13, p.19); the maximizer is such a rectangle
--   - generalization: n > 1 (the setting of Lemma 4.3, whose proof §4.1 is) → every n; reason: for n ≤ 1 the statement is immediate (no u or an empty [n]∖{u}); it specializes to n > 1
--   - encoding: log|𝒜_(u,v) × ℬ_(u,v)| → Real.logb 2 of |Auv 𝒜 u v| · |Buv ℬ u v|, with 𝒜_(u,v) stored as maps {x // x ≠ u} → Fin n; reason: |𝒜 × ℬ| = |𝒜|·|ℬ|; distinct restrictions are distinct maps, so the cardinalities agree
--   - encoding: [n], b⁻¹a, n = N/2 → Fin n (0-based), b⁻¹ * a (apply a first), bConn n; reason: Lean conventions; same instances
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), proof of Lemma 4.3 (§4.1), p.11 (PDF p.13), "Nevertheless, Lemma 4.4 implies that log|𝒜_(u,v) × ℬ_(u,v)| ≤ S_{n−1}"

import Mathlib
import Definitions.Def_NondetConn_bConn
import Definitions.Def_NondetConn_S
import Definitions.Def_NondetConn_Auv
import Definitions.Def_NondetConn_Buv

namespace NondetConn

/-- **Proof of Lemma 4.3, renaming bound** (Zhang, *Settling Nondeterministic Communication Complexity of Graph Connectivity*, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), §4.1, p.11:
"Lemma 4.4 implies that log|𝒜_(u,v) × ℬ_(u,v)| ≤ S_{n−1}").
Let `𝒜 × ℬ` be a 1-monochromatic rectangle of `bConn_N` (`N = 2n`) and `u, v ∈ [n]` with
`a(u) = v` for some `a ∈ 𝒜`. Then `log₂ (|𝒜_(u,v)| · |ℬ_(u,v)|) ≤ S_{n−1}`.

**Formalization Note** Stated for every 1-monochromatic rectangle (not only the maximizer of
`S_n`). `𝒜_(u,v)` and `ℬ_(u,v)` are `Auv` and `Buv`; the renaming of `[n] \ {u}` and
`[n] \ {v}` to `[n − 1]` is part of the proof. -/
theorem rectangle_restrict_le (n : ℕ) (𝒜 ℬ : Finset (Equiv.Perm (Fin n)))
    (hrect : ∀ a ∈ 𝒜, ∀ b ∈ ℬ, bConn n a b) (u v : Fin n) (huv : ∃ a ∈ 𝒜, a u = v) :
    Real.logb 2 (((Auv 𝒜 u v).card * (Buv ℬ u v).card : ℕ) : ℝ) ≤ S (n - 1) := by sorry

end NondetConn
