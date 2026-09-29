-- Prove2me | Theorems.Thm_Matrix_exists_forall_existsUnique_eq_apply_of_squarefree_of_card_eq
-- name    : Matrix.exists_forall_existsUnique_eq_apply_of_squarefree_of_card_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/0f3558d5-2776-521e-9f67-9eb9c49c90ea
-- title:
--   Rank-one freeness of M₂(ℤ/N)-modules of order N⁴
-- statement:
--   Let $N$ be a natural number, nonzero, and squarefree, and let $V$ be a finite abelian group equipped with a $\mathbb{Z}/N$-module structure whose cardinality satisfies $\mathrm{card}\, V = N^4$. Let $\alpha : M_2(\mathbb{Z}/N) \to \operatorname{End}_{\mathbb{Z}/N}(V)$ be a homomorphism of rings, where $M_2(\mathbb{Z}/N)$ is the ring of $2 \times 2$ matrices over $\mathbb{Z}/N$ indexed by `Fin 2` and $\operatorname{End}_{\mathbb{Z}/N}(V)$ is the ring of $\mathbb{Z}/N$-linear endomorphisms of $V$ (so $\alpha$ preserves $1$, hence $\alpha(1)$ acts as the identity on $V$). The assertion is that there exists $v_0 \in V$ such that for every $w \in V$ there is a unique matrix $a \in M_2(\mathbb{Z}/N)$ with $w = \alpha(a)\,v_0$. Equivalently, the $\mathbb{Z}/N$-linear map $M_2(\mathbb{Z}/N) \to V$, $a \mapsto \alpha(a) v_0$, is bijective: $v_0$ is a free generator of $V$ as a module over $M_2(\mathbb{Z}/N)$ via $\alpha$, so $V$ is free of rank one over $M_2(\mathbb{Z}/N)$. Note that the conclusion is stated as the existence of such a generator together with existence and uniqueness of coordinates, not as an abstract isomorphism of modules.
--
--   This is the rank-one freeness statement for modules over the split matrix order $M_2(\mathbb{Z}/N)$ at squarefree level: a module of the minimal possible cardinality $N^4$ over which $M_2(\mathbb{Z}/N)$ acts must be free on a single generator. It is used in the quaternionic part of the development, in the construction of Eichler orders and in the computation of centralisers of maximal orders for fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_exists_forall_existsUnique_eq_apply_of_squarefree_of_card_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Matrix.exists_forall_existsUnique_eq_apply_of_squarefree_of_card_eq
    (N : ℕ) [NeZero N] (hN : Squarefree N) (V : Type) [AddCommGroup V] [Module (ZMod N) V] [Finite V]
    (hV : Nat.card V = N ^ 4) (α : Matrix (Fin 2) (Fin 2) (ZMod N) →+* Module.End (ZMod N) V) :
    ∃ v₀ : V, ∀ w : V, ∃! a : Matrix (Fin 2) (Fin 2) (ZMod N), w = α a v₀ := by sorry
