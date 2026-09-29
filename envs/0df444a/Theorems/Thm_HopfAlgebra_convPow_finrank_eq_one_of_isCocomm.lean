-- Prove2me | Theorems.Thm_HopfAlgebra_convPow_finrank_eq_one_of_isCocomm
-- name    : HopfAlgebra.convPow_finrank_eq_one_of_isCocomm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/b99d1ce3-4d25-5e81-a135-de9447024171
-- title:
--   Deligne's theorem: a point is killed by the rank
-- statement:
--   Let $R$ be a commutative ring and let $H$ be a commutative ring carrying the structure of a Hopf algebra over $R$ whose comultiplication is cocommutative, and which is finite and free as an $R$-module; write $m = \operatorname{finrank}_R H$ for its rank. Let $T$ be a further commutative ring equipped with an $R$-algebra structure, and let $f$ be an $R$-algebra homomorphism $H \to T$, regarded as an element of the monoid `WithConv (H →ₐ[R] T)`, that is, of the set of such homomorphisms with the convolution product $(f * g)(h) = \sum f(h_{(1)})\,g(h_{(2)})$, whose unit element is $h \mapsto \varepsilon(h)\cdot 1_T$ for $\varepsilon$ the counit of $H$. The assertion is that the $m$-th convolution power of $f$ is the unit: $f^{m} = 1$ in this monoid. Geometrically, with $G = \operatorname{Spec} H$ the finite flat commutative group scheme of order $m$ over $R$ determined by $H$, every $T$-valued point of $G$ is annihilated by $m$.
--
--   This is Deligne's theorem that a finite flat commutative group scheme is killed by its order, stated pointwise on $T$-valued points for a commutative cocommutative Hopf algebra that is finite free over the base. It is used in the treatment of finite flat group schemes (injectivity of reduction maps on points, and the standing hypothesis that the points are killed by the order) and in the group-law and Cerednik–Drinfeld components that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_convPow_finrank_eq_one_of_isCocomm.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

theorem HopfAlgebra.convPow_finrank_eq_one_of_isCocomm
    (R : Type u) [CommRing R]
    (H : Type v) [CommRing H] [HopfAlgebra R H] [Coalgebra.IsCocomm R H]
    [Module.Finite R H] [Module.Free R H]
    (T : Type w) [CommRing T] [Algebra R T] (f : WithConv (H →ₐ[R] T)) :
    f ^ Module.finrank R H = 1 := by sorry
