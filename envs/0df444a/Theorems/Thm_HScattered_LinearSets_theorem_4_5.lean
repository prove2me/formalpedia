-- Prove2me | Theorems.Thm_HScattered_LinearSets_theorem_4_5
-- name    : HScattered.LinearSets.theorem_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:31:51.342997+00:00
-- url     : https://prove2.me/theorems/621924d6-d202-439b-bd60-9a812c1e1ed0
-- title:
--   Theorem 4.5 — for h ≥ 2, h-scattered linear sets are PΓL-equivalent iff their subspaces are ΓL-equivalent
-- statement:
--   Let $V = V(r,q^n)$ be an $r$-dimensional vector space over the finite field $\mathbb F_{q^n}$, let $h \ge 2$, and let $U$, $W$ be $h$-scattered $\mathbb F_q$-subspaces of $V$, so that $L_U$ and $L_W$ are $h$-scattered linear sets of $\mathrm{PG}(r-1,q^n)$. Then
--
--   $$
--   L_U \text{ and } L_W \text{ are } \mathrm{P}\Gamma\mathrm{L}(r,q^n)\text{-equivalent} \iff U \text{ and } W \text{ are } \Gamma\mathrm{L}(r,q^n)\text{-equivalent}.
--   $$
--
--   The "if" direction holds for all subspaces, because $L_{U^f} = L_U^{\varphi_f}$. The "only if" direction fails for $h = 1$: there are maximum scattered subspaces of $V(2,q^n)$ in different $\Gamma\mathrm L(2,q^n)$-orbits defining equivalent linear sets. For $h\ge 2$ the theorem turns the classification of $h$-scattered linear sets into the classification of their defining subspaces.
--
--   **Formalization Note** Both equivalences are taken with respect to arbitrary semilinear bijections `f : V ≃+ V` (with some field automorphism `σ : K ≃+* K`), not just linear ones; $\mathrm{P}\Gamma\mathrm{L}$-equivalence asks that the induced collineation $P \mapsto \langle f(P)\rangle_{\mathbb F_{q^n}}$ map $L_U$ onto $L_W$. Since $h$-scattered includes $h \le r-1$, the hypotheses force $r \ge 3$.
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 14, Theorem 4.5

import Mathlib
import Definitions.Def_HScattered_Bound_IsHScattered
import Definitions.Def_HScattered_LinearSets_LinearSet
import Definitions.Def_HScattered_LinearSets_Equivalence

namespace HScattered.LinearSets

/-- Theorem 4.5 (arXiv:1906.10590v2, p. 14). Let `L_U` and `L_W` be `h`-scattered linear sets
of `V(r, qⁿ)` with `h ≥ 2`. They are `PΓL(r, qⁿ)`-equivalent if and only if `U` and `W` are
`ΓL(r, qⁿ)`-equivalent. -/
theorem theorem_4_5 {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [Fintype F] [Fintype K] [FiniteDimensional K V]
    (h : ℕ) (hh : 2 ≤ h) (U W : Submodule F V)
    (hU : HScattered.Bound.IsHScattered F K h U) (hW : HScattered.Bound.IsHScattered F K h W) :
    PGammaLEquivalent F K U W ↔ GammaLEquivalent F K U W := by sorry

end HScattered.LinearSets
