-- Prove2me | Theorems.Thm_HopfAlgebra_formallyUnramified_of_ker_counit_eq_sq
-- name    : HopfAlgebra.formallyUnramified_of_ker_counit_eq_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/e14abfa7-b6b8-5a08-8841-3412361a409f
-- title:
--   Idempotent augmentation ideal forces formal unramifiedness
-- statement:
--   Let $R$ be a commutative ring and let $H$ be a commutative ring carrying the structure of a Hopf algebra over $R$, with counit $\varepsilon\colon H\to R$ (as an $R$-algebra homomorphism, `Bialgebra.counitAlgHom R H`). Write $I=\ker\varepsilon$ for the augmentation ideal of $H$. The hypothesis is that $I$ is idempotent, i.e. $I=I^{2}$ as ideals of $H$. The conclusion is that $H$ is formally unramified over $R$ in the sense of Mathlib's `Algebra.FormallyUnramified`: for every commutative $R$-algebra $B$ and every ideal $J\subseteq B$ with $J^{2}=0$, any two $R$-algebra homomorphisms $H\to B$ that become equal after composition with $B\to B/J$ coincide; equivalently, $\Omega_{H/R}=0$. No finiteness, flatness or connectedness assumption is imposed on $H$, and no hypothesis on $R$ beyond commutativity; the idempotence of the augmentation ideal is the only input besides the Hopf algebra structure (in particular the antipode, which enters the proof).
--
--   This is the unramified half of the classical computation of invariant differentials on an affine group scheme, where $\Omega_{H/R}$ is recovered from the augmentation ideal $I/I^{2}$: vanishing of $I/I^{2}$ propagates, via translation by the antipode, to vanishing of the module of differentials. It feeds the étaleness criteria for Hopf algebras used in the project, in particular [`HopfAlgebra.etale_of_pow_eq_one_of_isUnit_of_finite`](thm.html#HopfAlgebra.etale_of_pow_eq_one_of_isUnit_of_finite) and the construction of connected–étale sequences over $\mathbb{Z}_p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_formallyUnramified_of_ker_counit_eq_sq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem HopfAlgebra.formallyUnramified_of_ker_counit_eq_sq
    {R : Type u} [CommRing R] {H : Type v} [CommRing H] [HopfAlgebra R H]
    (hI : RingHom.ker (Bialgebra.counitAlgHom R H) = RingHom.ker (Bialgebra.counitAlgHom R H) ^ 2) :
    Algebra.FormallyUnramified R H := by sorry
