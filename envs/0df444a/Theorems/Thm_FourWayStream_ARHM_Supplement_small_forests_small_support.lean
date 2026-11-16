-- Prove2me | Theorems.Thm_FourWayStream_ARHM_Supplement_small_forests_small_support
-- name    : FourWayStream.ARHM.Supplement.small_forests_small_support
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:03:35.104203+00:00
-- url     : https://prove2.me/theorems/29793d0b-934d-4219-b120-b0b7efce117d
-- title:
--   Lemma B.2 — small forests have small support: $|V(F)|\le2\,\mathrm{fs}(F)$
-- statement:
--   For every nonempty set $F$ of edges (no loops) of a graph on $[N]$,
--   $$|V(F)|\le2\,\mathrm{fs}(F),$$
--   where $V(F)$ is the set of endpoints and $\mathrm{fs}(F)=|V(F)|-c(F)$ the forest size. Consequently, if $M_1,\dots,M_m$ are perfect matchings of $[N]$ ($N\ge2$) with $\tau_{\mathrm{for}}(M_1,\dots,M_m)\le s$, then some set $W$ of at most $2s$ vertices contains an edge of every $M_t$ (both endpoints in $W$).
--
--   This turns a small transversal forest into a small vertex set that every matching must hit, which Proposition B.3 bounds by a union bound.
--
--   **Formalization Note** Edge sets are finite sets of unordered pairs; "contains an edge" means both endpoints lie in $W$.
--
--   Differences from the source:
--   - encoding: an edge set (graph convention of §6.2); N ≥ 2 (standing assumption of §6.2) → the hypothesis that no edge of F is a loop; 2 ≤ N for the consequence; reason: nondegeneracy conditions that only exclude objects outside the paper’s setting (a loop is not an edge; there are no perfect matchings of the empty vertex set to which the consequence applies)
--   - encoding: [N], [m], [w], [r], [n], bits in {0,1}, edges {u, v} → Fin N, Fin m, Fin w, Fin r, Fin n (0-based), Bool, Sym2; reason: Lean convention; same instances
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), p.44, Lemma B.2

import Mathlib
import Definitions.Def_FourWayStream_ARHM_Stream
import Definitions.Def_FourWayStream_ARHM_Information
import Definitions.Def_FourWayStream_ARHM_Protocols
import Definitions.Def_FourWayStream_ARHM_Supplement_Simultaneous

set_option autoImplicit false
open Classical

namespace FourWayStream.ARHM.Supplement

open QAlgorithms
open scoped Matrix

/-- Lemma B.2 (Small forests have small support), p.44. For every nonempty set `F` of (nonloop)
edges, `|V(F)| ≤ 2 fs(F)`. Consequently, for perfect matchings `M_1, …, M_m` of `[N]` (`N ≥ 2`), if
`τ_for(M_1, …, M_m) ≤ s` then some set `W` of at most `2s` vertices contains an edge of every
`M_t`. -/
theorem small_forests_small_support (N : ℕ) :
    (∀ F : Finset (Sym2 (Fin N)), F.Nonempty → (∀ e ∈ F, ¬ e.IsDiag) →
      (edgeVerts F).card ≤ 2 * forestSize F) ∧
    (2 ≤ N → ∀ (m s : ℕ) (Ms : Fin m → Finset (Sym2 (Fin N))), (∀ t, IsPerfectMatching (Ms t)) →
      tauFor Ms ≤ s →
      ∃ W : Finset (Fin N), W.card ≤ 2 * s ∧ ∀ t, ∃ e ∈ Ms t, ∀ v ∈ e, v ∈ W) := by sorry

end FourWayStream.ARHM.Supplement
