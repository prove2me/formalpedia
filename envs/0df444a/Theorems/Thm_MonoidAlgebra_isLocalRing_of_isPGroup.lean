-- Prove2me | Theorems.Thm_MonoidAlgebra_isLocalRing_of_isPGroup
-- name    : MonoidAlgebra.isLocalRing_of_isPGroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/7ce0fa38-2284-5b44-be60-d8d4bda77e9a
-- title:
--   Group ring of a finite abelian p-group is local
-- statement:
--   Let $\mathcal O$ be a commutative ring that is local (so it has a unique maximal ideal $\mathfrak m_{\mathcal O}$, in Mathlib's `IsLocalRing` sense), let $p$ be a prime number, and assume that the image of $p$ under the canonical map $\mathbb N \to \mathcal O$ lies in $\mathfrak m_{\mathcal O}$. Let $G$ be a commutative group that is finite and that is a $p$-group in the sense of `IsPGroup p G`, i.e. every element of $G$ is killed by some power of $p$. The conclusion is that the monoid algebra $\mathcal O[G]$, namely `MonoidAlgebra 𝒪 G` (finitely supported functions $G \to \mathcal O$ with convolution product), is again a local ring. No completeness or Noetherian hypothesis on $\mathcal O$ is imposed, and $\mathcal O$ is not assumed to have residue characteristic exactly $p$ beyond the stated condition $p \in \mathfrak m_{\mathcal O}$; the two hypotheses $p \in \mathfrak m_{\mathcal O}$ and $G$ a $p$-group are both needed, since otherwise $\mathcal O[G]$ acquires non-trivial idempotents.
--
--   This is the standard fact that the group ring of a finite abelian $p$-group over a local ring of residue characteristic divisible by $p$ is local, with maximal ideal the preimage of $\mathfrak m_{\mathcal O}$ under the augmentation. It is used in the Taylor–Wiles patching apparatus, where the diamond group ring $\mathcal O[\Delta_Q]$ must be a local $\mathcal O$-algebra; it is cited by the construction of the Hecke ring at Taylor–Wiles level, by the comparison of $\mathcal O[\Delta_Q]$-module bases, and by the presentation of $\mathcal O[G]$ as a quotient of a power series ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MonoidAlgebra_isLocalRing_of_isPGroup.lean

import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.GroupTheory.PGroup
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem MonoidAlgebra.isLocalRing_of_isPGroup {𝒪 : Type u} [CommRing 𝒪] [IsLocalRing 𝒪] {p : ℕ} [Fact p.Prime] (hp : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪) {G : Type v} [CommGroup G] [Finite G] (hG : IsPGroup p G) : IsLocalRing (MonoidAlgebra 𝒪 G) := by sorry
