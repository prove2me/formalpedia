-- Prove2me | Theorems.Thm_LocalSepDecomp_lemma_5_1
-- name    : LocalSepDecomp.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:43:37.582201+00:00
-- url     : https://prove2.me/theorems/d7e84861-4101-4ff2-aadc-1dd026d75422
-- title:
--   Lemma 5.1 — the displacement exceeds $r$
-- statement:
--   For every connected graph $G$ and every $r\in\mathbb N$, the displacement of the $r$-local covering satisfies
--   $$\Delta_r(G)>r,$$
--   where $\Delta_r(G)$ is the least distance in $G_r$ between two distinct vertices with the same image (and $\infty$ if there are none).
--
--   Consequently the theory works for all $r$-local separations of order at most $2$, whatever $G$ and $r>0$.
--
--   Differences from the source:
--   - encoding: the r-local covering $p_r : G_r \to G$, unique up to isomorphism of coverings → an arbitrary covering $p : C \to G$ with `IsLocalCovering G r p` (characteristic subgroup = the r-local subgroup), on a vertex type in the universe of $V$; reason: the paper constructs $G_r$ only up to isomorphism; every statement holds for one such covering iff for all, and one exists in the universe of $V$ (walks modulo the r-local subgroup)
-- source:
--   Jacobs, Knappe, Kurkofka, Canonical Graph Decompositions via Local Separations, preprint (STOC 2027 submission, arXiv:2501.16170; sha256 9a11d48d…), Lemma 5.1, p.31

import Mathlib
import Definitions.Def_LocalSepDecomp_Cutouts

set_option autoImplicit false

namespace LocalSepDecomp

open SimpleGraph

universe u

/-- **Lemma 5.1.** R. W. Jacobs, P. Knappe, J. Kurkofka, *Canonical Graph Decompositions via Local Separations*,
preprint (STOC 2027 submission, arXiv:2501.16170; sha256 9a11d48d…), Lemma 5.1, p.31.
`Δ_r(G) > r` for every connected graph `G` and `r ∈ ℕ`.

**Formalization Note.** `Δ_r(G)` is the displacement (in `ℕ∞`, `min ∅ = ∞`) of any `r`-local
covering `p` of `G`. -/
theorem lemma_5_1 {V W : Type u} (G : SimpleGraph V) (hG : G.Connected) (r : ℕ)
    (C : SimpleGraph W) (p : C →g G) (hp : IsLocalCovering G r p) :
    (r : ℕ∞) < displacement p := by sorry

end LocalSepDecomp
