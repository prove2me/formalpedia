-- Prove2me | Theorems.Thm_JuschenkoMonod_isAmenable_of_isAmenable_stabilizer_symmDiff_natSet
-- name    : JuschenkoMonod.isAmenable_of_isAmenable_stabilizer_symmDiff_natSet
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T17:27:44.73406+00:00
-- url     : https://prove2.me/theorems/aa258c5a-2d8f-4126-bab8-607cfb441fbd
-- title:
--   Proposition 3.3 — a subgroup of W(ℤ) is amenable if its stabilisers of the sets E △ ℕ, E finite, are amenable
-- statement:
--   Let $G$ be a subgroup of $W(\mathbf Z)$. Suppose that for every finite set $E \subseteq \mathbf Z$, the stabiliser in $G$ of the set $E \mathbin{\triangle} \mathbf N$ (the $g \in G$ with $g(E \mathbin{\triangle} \mathbf N) = E \mathbin{\triangle} \mathbf N$) is amenable. Then $G$ is amenable. Here $\mathbf N = \{0, 1, 2, \dots\} \subseteq \mathbf Z$.
--
--   *Formalization note.* "$G < W(\mathbf Z)$ be a subgroup" is read as any subgroup, $W(\mathbf Z)$ itself included. $\mathbf N$ is taken to contain $0$.
-- source:
--   Juschenko, K. and Monod, N., Cantor systems, piecewise translations and simple amenable groups, Ann. of Math. (2) 178 (2013) 775–787, https://doi.org/10.4007/annals.2013.178.2.7, pp. 784–785, Proposition 3.3

import Mathlib
import Definitions.Def_Garrido_Amenability
import Definitions.Def_IntervalExchange
import Definitions.Def_JuschenkoMonod

open scoped Pointwise

namespace JuschenkoMonod

theorem isAmenable_of_isAmenable_stabilizer_symmDiff_natSet (G : Subgroup (Equiv.Perm ℤ))
    (hG : G ≤ IntervalExchange.wobbling ℤ)
    (h : ∀ E : Finset ℤ, Garrido.IsAmenable (MulAction.stabilizer G (symmDiff (E : Set ℤ) natSet))) :
    Garrido.IsAmenable G := by
  sorry

end JuschenkoMonod
