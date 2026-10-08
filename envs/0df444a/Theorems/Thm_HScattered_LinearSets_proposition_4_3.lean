-- Prove2me | Theorems.Thm_HScattered_LinearSets_proposition_4_3
-- name    : HScattered.LinearSets.proposition_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:28:56.25436+00:00
-- url     : https://prove2.me/theorems/5a1e0e63-6d9f-4b83-becf-b25f520eb443
-- title:
--   Proposition 4.3 — the rank of a linear set scattered with respect to lines is uniquely defined
-- statement:
--   Let $V = V(r,q^n)$ and let $U$ be a $2$-scattered $\mathbb F_q$-subspace of $V$, so that $L_U$ is scattered with respect to lines of $\mathrm{PG}(r-1,q^n) = \mathrm{PG}(V,\mathbb F_{q^n})$. Then the rank of $L_U$ is uniquely defined: for every $\mathbb F_q$-subspace $W$ of $V$,
--
--   $$
--   L_W = L_U \quad\Longrightarrow\quad \dim_{\mathbb F_q} W = \dim_{\mathbb F_q} U .
--   $$
--
--   For general linear sets this fails: for instance all $\mathbb F_q$-linear sets of rank at least $rn - n + 1$ coincide with the whole space. The proposition is the first step in the proof of Lemma 4.4.
--
--   **Formalization Note** "Scattered with respect to lines" is Definition 4.1's $2$-scattered, including the spanning condition $\langle U\rangle_{\mathbb F_{q^n}} = V$ and the range $2 \le r-1$ of Definition 1.1. $W$ is an arbitrary $\mathbb F_q$-subspace.
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 13, Proposition 4.3

import Mathlib
import Definitions.Def_HScattered_Bound_IsHScattered
import Definitions.Def_HScattered_LinearSets_LinearSet

namespace HScattered.LinearSets

/-- Proposition 4.3 (arXiv:1906.10590v2, p. 13). If `L_U` is scattered with respect to lines
(i.e. `U` is a 2-scattered `𝔽_q`-subspace of `V = V(r, qⁿ)`, Definition 4.1), then its rank is
uniquely defined: every `𝔽_q`-subspace `W` of `V` with `L_W = L_U` has
`dim_{𝔽_q} W = dim_{𝔽_q} U`. -/
theorem proposition_4_3 {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [Fintype F] [Fintype K] [FiniteDimensional K V]
    (U : Submodule F V) (hU : HScattered.Bound.IsHScattered F K 2 U)
    (W : Submodule F V) (hW : linearSet F K W = linearSet F K U) :
    Module.finrank F W = Module.finrank F U := by sorry

end HScattered.LinearSets
