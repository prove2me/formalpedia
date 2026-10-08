-- Prove2me | Theorems.Thm_HScattered_Construction_theorem_2_3
-- name    : HScattered.Construction.theorem_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:16.036172+00:00
-- url     : https://prove2.me/theorems/93114e04-be3d-4db9-8b00-3db15dfa623c
-- title:
--   Theorem 2.3 — an h-scattered subspace defines a subgeometry or has dimension ≤ rn/(h + 1)
-- statement:
--   Let $V$ be an $r$-dimensional $\mathbb F_{q^n}$-vector space and $U$ an $h$-scattered $\mathbb F_q$-subspace of $V$. Then either
--
--   1. $\dim_{\mathbb F_q}U=r$, $U$ defines a subgeometry of $\mathrm{PG}(V,\mathbb F_{q^n})$, and $U$ is $(r-1)$-scattered; or
--   2. $U$ satisfies the bound
--
--   $$
--   \dim_{\mathbb F_q} U\le \frac{rn}{h+1}. \tag{1}
--   $$
--
--   This is the paper's main bound; for $h=1$ it is the Blokhuis–Lavrauw bound $rn/2$. In this mission it supplies maximality: when $n\ge h+1$ one has $r\le rn/(h+1)$, so an $h$-scattered subspace of dimension exactly $rn/(h+1)$ is maximum.
--
--   **Formalization Note** The bound is stated as $(h+1)\dim_{\mathbb F_q}U\le rn$, with $r=\dim_{\mathbb F_{q^n}}V$ and $n=\dim_{\mathbb F_q}\mathbb F_{q^n}$, to avoid natural-number division. In the first alternative $r-1$ is natural-number subtraction, harmless because $h$-scatteredness forces $r\ge 2$. This statement duplicates the goal of the companion mission on the dimension bound and is restated here because the maximality in Theorem 2.6 depends on it.
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 4, Theorem 2.3

import Mathlib
import Definitions.Def_HScattered_Construction_IsHScattered
import Definitions.Def_HScattered_Construction_DefinesSubgeometry

namespace HScattered.Construction

/-- Theorem 2.3 (arXiv:1906.10590v2, p. 4): an h-scattered `𝔽_q`-subspace `U` of the
r-dimensional `𝔽_{qⁿ}`-space `V` either has dimension `r`, defines a subgeometry of
`PG(V, 𝔽_{qⁿ})` and is (r − 1)-scattered, or satisfies `dim_{𝔽_q} U ≤ rn/(h + 1)`
(stated as `(h + 1) · dim_{𝔽_q} U ≤ r · n`). -/
theorem theorem_2_3 {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [Fintype F] [Fintype K] [FiniteDimensional K V]
    (h : ℕ) (U : Submodule F V) (hU : HScattered.Bound.IsHScattered F K h U) :
    (Module.finrank F U = Module.finrank K V ∧ DefinesSubgeometry F K U ∧
        HScattered.Bound.IsHScattered F K (Module.finrank K V - 1) U) ∨
      (h + 1) * Module.finrank F U ≤ Module.finrank K V * Module.finrank F K := by sorry

end HScattered.Construction
