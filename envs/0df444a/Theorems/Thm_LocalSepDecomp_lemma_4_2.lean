-- Prove2me | Theorems.Thm_LocalSepDecomp_lemma_4_2
-- name    : LocalSepDecomp.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:44:48.65458+00:00
-- url     : https://prove2.me/theorems/8f724448-a9f0-4455-a999-a6564152acd9
-- title:
--   Lemma 4.2 — tight $r$-local separators are $r$-tomic
-- statement:
--   Let $G$ be a connected graph and $r\in\mathbb N$. Every tight $r$-local separator $X$ of $G$ is $r$-tomic: any two vertices of $X$ are linked by a concatenation of $r$-local $X$-paths.
--
--   Separators of $r$-local bottlenecks are therefore $r$-tomic, which is the hypothesis under which the paper's correspondences and lifting results apply.
--
--   Differences from the source: none.
-- source:
--   Jacobs, Knappe, Kurkofka, Canonical Graph Decompositions via Local Separations, preprint (STOC 2027 submission, arXiv:2501.16170; sha256 9a11d48d…), Lemma 4.2, p.25

import Mathlib
import Definitions.Def_LocalSepDecomp_Cutouts

set_option autoImplicit false

namespace LocalSepDecomp

open SimpleGraph

universe u

/-- **Lemma 4.2.** R. W. Jacobs, P. Knappe, J. Kurkofka, *Canonical Graph Decompositions via Local Separations*,
preprint (STOC 2027 submission, arXiv:2501.16170; sha256 9a11d48d…), Lemma 4.2, p.25.
Every tight `r`-local separator of a connected graph `G` is `r`-tomic. -/
theorem lemma_4_2 {V : Type u} (G : SimpleGraph V) (hG : G.Connected) (r : ℕ) (X : Set V)
    (hX : IsTightRLocalSeparator G r X) : IsRTomic G r X := by sorry

end LocalSepDecomp
