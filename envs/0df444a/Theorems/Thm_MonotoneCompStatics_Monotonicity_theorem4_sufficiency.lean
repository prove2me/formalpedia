-- Prove2me | Theorems.Thm_MonotoneCompStatics_Monotonicity_theorem4_sufficiency
-- name    : MonotoneCompStatics.Monotonicity.theorem4_sufficiency
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:33:06.899985+00:00
-- url     : https://prove2.me/theorems/1e064aaa-13a7-429a-bc7b-cabaa9661d17
-- title:
--   Theorem 4, proof (⇐): ordinal conditions imply monotonicity
-- statement:
--   Let $X$ be a lattice, $T$ a partially ordered set, and $f:X\times T\to\mathbb R$. Suppose $f(\cdot,t)$ is quasisupermodular on $X$ for every $t\in T$ and $f$ has the single crossing property in $(x;t)$. Then its maximizer correspondence $M(t,S)=\operatorname{argmax}_{x\in S}f(x,t)$ obeys
--
--   $$t\le t',\quad S\le_s S'\quad\Longrightarrow\quad M(t,S)\le_s M(t',S')$$
--
--   for all parameter pairs and all constraint sets. This is the sufficient direction of the paper's Monotonicity Theorem.
--
--   **Formalization Note** The definition of $M$ allows empty maximizer sets. Quasisupermodularity is on all of $X$, and single crossing includes both weak and strict implications.
-- source:
--   Milgrom and Shannon, Monotone Comparative Statics, Econometrica 62 (1994), p. 162 (PDF 7), Theorem 4, proof (⇐)

import Mathlib
import Definitions.Def_MonotoneCompStatics_Monotonicity_ArgmaxMonotone
import Definitions.Def_MonotoneCompStatics_Monotonicity_QuasiSupermodularOn
import Definitions.Def_MonotoneCompStatics_Monotonicity_SingleCrossing

namespace MonotoneCompStatics.Monotonicity

theorem theorem4_sufficiency {X T : Type*} [Lattice X] [PartialOrder T] (f : X → T → ℝ)
    (hq : ∀ t, QuasiSupermodularOn (fun x => f x t) Set.univ) (hsc : SingleCrossing f) :
    ArgmaxMonotone f := by sorry

end MonotoneCompStatics.Monotonicity
