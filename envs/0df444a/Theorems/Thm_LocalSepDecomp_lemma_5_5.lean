-- Prove2me | Theorems.Thm_LocalSepDecomp_lemma_5_5
-- name    : LocalSepDecomp.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:44:00.355914+00:00
-- url     : https://prove2.me/theorems/83a509f9-4505-4929-a24a-54ef0aeade47
-- title:
--   Lemma 5.5 — for $r\le 2$ tight $r$-local separators are single vertices
-- statement:
--   Let $G$ be a connected graph and $r\le 2$. Then every tight $r$-local separator $X$ of $G$ has size $|X|=1$.
--
--   This is used in §9 to reduce Theorem 1 to the case $r\ge 2$ or $k=1$.
--
--   Differences from the source:
--   - encoding: orders $|X|$ of separators → `Set.encard` in $\mathbb N_\infty$; reason: separators of the infinite cover can be infinite (p.29); no finite instance changes
-- source:
--   Jacobs, Knappe, Kurkofka, Canonical Graph Decompositions via Local Separations, preprint (STOC 2027 submission, arXiv:2501.16170; sha256 9a11d48d…), Lemma 5.5, p.32

import Mathlib
import Definitions.Def_LocalSepDecomp_Cutouts

set_option autoImplicit false

namespace LocalSepDecomp

open SimpleGraph

universe u

/-- **Lemma 5.5.** R. W. Jacobs, P. Knappe, J. Kurkofka, *Canonical Graph Decompositions via Local Separations*,
preprint (STOC 2027 submission, arXiv:2501.16170; sha256 9a11d48d…), Lemma 5.5, p.32.
Let `G` be connected and `r ≤ 2`. Then every tight `r`-local separator of `G` has size `1`. -/
theorem lemma_5_5 {V : Type u} (G : SimpleGraph V) (hG : G.Connected) (r : ℕ) (hr : r ≤ 2)
    (X : Set V) (hX : IsTightRLocalSeparator G r X) : X.encard = 1 := by sorry

end LocalSepDecomp
