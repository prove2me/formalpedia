-- Prove2me | Theorems.Thm_IsLocalRing_maximalIdeal_eq_of_le_sup_sq
-- name    : IsLocalRing.maximalIdeal_eq_of_le_sup_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/411922cd-b8b7-5b82-8d11-71ff610a6622
-- title:
--   Nakayama criterion: 𝔪 = N when 𝔪 ≤ N + 𝔪²
-- statement:
--   Let $R$ be a commutative ring that is local (in the sense of Mathlib's `IsLocalRing`, so it has a unique maximal ideal `maximalIdeal R`, written $\mathfrak{m}$ below) and Noetherian, and let $N$ be an ideal of $R$. Assume that $N \le \mathfrak{m}$ and that $\mathfrak{m} \le N \sqcup \mathfrak{m}^2$, the join being the sum of the two ideals. Then $\mathfrak{m} = N$. Thus an ideal contained in the maximal ideal which together with $\mathfrak{m}^2$ generates $\mathfrak{m}$ is already equal to $\mathfrak{m}$; equivalently, any lift to $\mathfrak{m}$ of a generating set of the cotangent space $\mathfrak{m}/\mathfrak{m}^2$ generates $\mathfrak{m}$. The statement is formulated for an arbitrary ideal $N$, with no finiteness hypothesis on $N$ itself; the Noetherian hypothesis is used only through the finite generation of $\mathfrak{m}$.
--
--   This is the standard consequence of Nakayama's lemma for Noetherian local rings: the maximal ideal is determined modulo its square. It is used in the verification that a suitable local ring is a two-dimensional regular local ring, via a criterion expressing $\mathfrak{m}$ in terms of two elements together with $\mathfrak{m}^2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_maximalIdeal_eq_of_le_sup_sq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open IsLocalRing

theorem IsLocalRing.maximalIdeal_eq_of_le_sup_sq
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (N : Ideal R) (hN : N ≤ maximalIdeal R) (h : maximalIdeal R ≤ N ⊔ maximalIdeal R ^ 2) :
    maximalIdeal R = N := by sorry
