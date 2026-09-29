-- Prove2me | Theorems.Thm_HopfAlgebra_exists_forall_pow_pow_eq_algebraMap_counit_of_isLocalRing_zmodp
-- name    : HopfAlgebra.exists_forall_pow_pow_eq_algebraMap_counit_of_isLocalRing_zmodp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/a14c35d4-0df7-5d58-8101-db64a1defdfc
-- title:
--   Frobenius is nilpotent on a finite local 𝔽ₚ-Hopf algebra
-- statement:
--   Let $p$ be a natural number assumed prime (as a `Fact` instance), and let $B$ be a commutative ring which is a Hopf algebra over $\mathbb{Z}/p$ and is finite as a $\mathbb{Z}/p$-module, together with the hypothesis `hB` that $B$ is a local ring. The assertion is that there exists a natural number $N$ with $0 < N$ such that for every $x \in B$ one has $x^{p^N} = \eta(\varepsilon(x))$, where $\varepsilon =$ `Coalgebra.counit` is the counit $B \to \mathbb{Z}/p$ of the coalgebra structure and $\eta$ is the structure map `algebraMap` $\mathbb{Z}/p \to B$. In other words, some positive iterate of the Frobenius endomorphism of $B$ coincides with the composite of the counit with the unit; all $p$-power maps $x \mapsto x^{p^N}$ for larger $N$ then agree with it as well, though only existence of one such $N$ is claimed. Dually, Frobenius is nilpotent on the finite connected group scheme $\operatorname{Spec} B$ over $\mathbb{F}_p$.
--
--   This is the standard statement that a finite connected (i.e. local) group scheme over $\mathbb{F}_p$ is killed by a power of Frobenius, in the affine-algebra formulation. It is used in the construction of the Néron-model objects attached to modular curves at $p$, where the connected part of a finite flat group scheme must be annihilated along a Frobenius-twisted operator identity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_forall_pow_pow_eq_algebraMap_counit_of_isLocalRing_zmodp.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem HopfAlgebra.exists_forall_pow_pow_eq_algebraMap_counit_of_isLocalRing_zmodp
    (p : ℕ) [Fact p.Prime]
    (B : Type) [CommRing B] [HopfAlgebra (ZMod p) B] [Module.Finite (ZMod p) B]
    (hB : IsLocalRing B) :
    ∃ N : ℕ, 0 < N ∧ ∀ x : B, x ^ p ^ N = algebraMap (ZMod p) B (Coalgebra.counit (R := ZMod p) x) := by sorry
