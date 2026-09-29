-- Prove2me | Theorems.Thm_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_finrank_eq_two_of_forall_isIdempotentElem
-- name    : HopfAlgebra.nonempty_bialgEquiv_monoidAlgebra_of_finrank_eq_two_of_forall_isIdempotentElem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/207e9fab-d012-55e3-96bb-6aecb9e0f3c1
-- title:
--   Connected rank-two Hopf algebra is R[ℤ/2]
-- statement:
--   Let $R$ be a commutative ring in which the element $2$ is irreducible, and let $H$ be a commutative ring equipped with the structure of a Hopf algebra over $R$ which, as an $R$-module, is finitely generated and free of rank $\operatorname{finrank}_R H = 2$. Assume further that $H$ has no idempotents besides the trivial ones: every $e \in H$ with $e^2 = e$ satisfies $e = 0$ or $e = 1$. Then the type of $R$-bialgebra equivalences between $H$ and the monoid algebra $R[\mathrm{Multiplicative}\,(\mathbb{Z}/2)]$, with its group-algebra comultiplication and counit, is nonempty; that is, there exists an isomorphism $H \cong R[\mathbb{Z}/2]$ of $R$-bialgebras. Note that the conclusion is an isomorphism of bialgebras (compatibility with the coalgebra structures is asserted, compatibility with the antipodes is not part of the statement), and that it is phrased as nonemptiness of the type of such equivalences rather than as a chosen equivalence.
--
--   In the language of group schemes: a finite flat commutative group scheme of order $2$ over a base in which $2$ is irreducible (for instance a discrete valuation ring with uniformiser $2$) whose underlying scheme is connected in the weak sense that $H$ has only trivial idempotents is the multiplicative group scheme $\mu_2$. This is the $p = 2$ case of the Tate–Oort classification of group schemes of prime order, in the form used to identify $2$-torsion subgroup schemes; it is cited in the analysis of character closures of points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_finrank_eq_two_of_forall_isIdempotentElem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem HopfAlgebra.nonempty_bialgEquiv_monoidAlgebra_of_finrank_eq_two_of_forall_isIdempotentElem
    {R : Type u} [CommRing R] (h2 : Irreducible (2 : R))
    (H : Type v) [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Free R H]
    (hrank : Module.finrank R H = 2) (hconn : ∀ e : H, IsIdempotentElem e → e = 0 ∨ e = 1) :
    Nonempty (H ≃ₐc[R] MonoidAlgebra R (Multiplicative (ZMod 2))) := by sorry
