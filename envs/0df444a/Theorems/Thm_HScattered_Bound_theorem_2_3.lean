-- Prove2me | Theorems.Thm_HScattered_Bound_theorem_2_3
-- name    : HScattered.Bound.theorem_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:38.506861+00:00
-- url     : https://prove2.me/theorems/e00c4bc4-31d1-41ac-b089-9fdbdf2fc10d
-- title:
--   Theorem 2.3 — an h-scattered subspace defines a subgeometry or has dimension at most rn/(h + 1)
-- statement:
--   Let $V$ be an $r$-dimensional vector space over $\mathbb F_{q^n}$ and let $U$ be an $h$-scattered $\mathbb F_q$-subspace of $V$ (so $0 < h \le r-1$). Then at least one of the following holds:
--
--   1. $\dim_{\mathbb F_q} U = r$, $U$ defines a subgeometry of $\mathrm{PG}(V,\mathbb F_{q^n})$, and $U$ is $(r-1)$-scattered;
--   2. $$\dim_{\mathbb F_q} U \le \frac{rn}{h+1}.$$
--
--   This is the main theorem of the paper. For $h = 1$ it is the bound $rn/2$ of Blokhuis and Lavrauw (2000) for scattered subspaces; for $h > 1$ it is new. Subspaces attaining the bound are maximum $h$-scattered, and for $h = r-1$ and dimension $n$ they correspond to MRD codes.
--
--   **Formalization Note** The second alternative is written without division as $(h+1)\cdot\dim_{\mathbb F_q} U \le r\cdot n$, with $n = \dim_{\mathbb F_q}\mathbb F_{q^n}$. "Either … or" is an inclusive disjunction: when $n = h+1$ both alternatives can hold. The range $0<h<r$ and the spanning condition are part of the hypothesis that $U$ is $h$-scattered. The statement covers every $h$, including $h = 1$, which the paper attributes to Blokhuis–Lavrauw. "$U$ defines a subgeometry" (a notion the paper uses without defining it) is the shared definition `HScattered.Construction.DefinesSubgeometry`: some $\mathbb F_q$-basis of $U$ is an $\mathbb F_{q^n}$-basis of $V$.
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 4, Theorem 2.3 (proof pp. 4–6)

import Mathlib
import Definitions.Def_HScattered_Bound_IsHScattered
import Definitions.Def_HScattered_Construction_DefinesSubgeometry

namespace HScattered.Bound

/-- Theorem 2.3 (arXiv:1906.10590v2, p. 4). Let `V` be an `r`-dimensional `𝔽_{qⁿ}`-vector space
and `U` an `h`-scattered `𝔽_q`-subspace of `V`. Then either `dim U = r`, `U` defines a
subgeometry of `PG(V, 𝔽_{qⁿ})` and `U` is `(r − 1)`-scattered, or `dim U ≤ rn/(h + 1)`
(stated as `(h + 1) · dim U ≤ r · n`). The disjunction is inclusive. -/
theorem theorem_2_3 {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [Fintype F] [Fintype K] [FiniteDimensional K V]
    (h : ℕ) (U : Submodule F V) (hU : IsHScattered F K h U) :
    (Module.finrank F U = Module.finrank K V ∧ HScattered.Construction.DefinesSubgeometry F K U ∧
        IsHScattered F K (Module.finrank K V - 1) U) ∨
      (h + 1) * Module.finrank F U ≤ Module.finrank K V * Module.finrank F K := by sorry

end HScattered.Bound
