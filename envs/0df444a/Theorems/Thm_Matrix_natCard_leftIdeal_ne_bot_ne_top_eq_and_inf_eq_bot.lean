-- Prove2me | Theorems.Thm_Matrix_natCard_leftIdeal_ne_bot_ne_top_eq_and_inf_eq_bot
-- name    : Matrix.natCard_leftIdeal_ne_bot_ne_top_eq_and_inf_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/45cec04e-bdb7-57e6-95c6-1b4d6b706f59
-- title:
--   The ℓ+1 proper left ideals of M₂(𝔽_ℓ)
-- statement:
--   Let $\ell$ be a prime, and consider the ring $M_2(\mathbb{Z}/\ell)$ of $2\times 2$ matrices over $\mathbb{Z}/\ell$ regarded as a module over itself, so that its submodules are precisely its left ideals. The assertion is a conjunction of two statements. First, the set of left ideals $I$ of $M_2(\mathbb{Z}/\ell)$ with $I \neq \bot$ and $I \neq \top$ — that is, neither the zero ideal nor the whole ring — has cardinality exactly $\ell + 1$ (the count is taken as a natural number via `Nat.card` of the corresponding subtype). Second, for any two left ideals $I, I'$ of $M_2(\mathbb{Z}/\ell)$, each different from $\bot$ and from $\top$, if $I \neq I'$ then $I \sqcap I' = \bot$: distinct proper non-zero left ideals intersect in the zero ideal.
--
--   The left ideals of $M_2(F)$ for a field $F$ correspond to the subspaces of $F^2$, so the proper non-zero ones correspond to the points of $\mathbb{P}^1(F)$; over $F = \mathbb{F}_\ell$ this gives the count $\ell+1$ and the triviality of pairwise intersections. It is used in the project to enumerate the $\ell+1$ extra level structures at $\ell$ arising from a maximal order in a quaternion algebra, by [`QuaternionAlgebra.IsMaximalOrder.natCard_properLine_eq_and_inf_eq`](thm.html#QuaternionAlgebra.IsMaximalOrder.natCard_properLine_eq_and_inf_eq), [`QuaternionAlgebra.IsMaximalOrder.exists_submodule_relIndex_eq_sq_and_transversal_of_levelModule`](thm.html#QuaternionAlgebra.IsMaximalOrder.exists_submodule_relIndex_eq_sq_and_transversal_of_levelModule) and [`CerednikDrinfeld.QM.FakeEllipticCurve.existsUnique_or_forall_reducesToZero_of_extraLevels`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.existsUnique_or_forall_reducesToZero_of_extraLevels).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_natCard_leftIdeal_ne_bot_ne_top_eq_and_inf_eq_bot.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion

theorem Matrix.natCard_leftIdeal_ne_bot_ne_top_eq_and_inf_eq_bot
    (ℓ : ℕ) [Fact ℓ.Prime] :
    Nat.card {I : Submodule (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) // I ≠ ⊥ ∧ I ≠ ⊤} = ℓ + 1 ∧
    ∀ I I' : Submodule (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (Matrix (Fin 2) (Fin 2) (ZMod ℓ)),
      I ≠ ⊥ → I ≠ ⊤ → I' ≠ ⊥ → I' ≠ ⊤ → I ≠ I' → I ⊓ I' = ⊥ := by sorry
