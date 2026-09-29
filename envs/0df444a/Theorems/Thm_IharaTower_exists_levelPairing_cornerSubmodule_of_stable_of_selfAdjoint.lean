-- Prove2me | Theorems.Thm_IharaTower_exists_levelPairing_cornerSubmodule_of_stable_of_selfAdjoint
-- name    : IharaTower.exists_levelPairing_cornerSubmodule_of_stable_of_selfAdjoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/2e3b8373-601b-5afd-87e3-bfc07075798a
-- title:
--   Perfect self-adjoint pairing restricts to a level pairing on a corner
-- statement:
--   Let $\mathcal O$ be a commutative ring, $\mathbb T$ a commutative $\mathcal O$-algebra, and $V$ an abelian group carrying compatible $\mathcal O$- and $\mathbb T$-module structures (a scalar tower). Let $W_0$ be an $\mathcal O$-submodule of $V$ which is stable under the $\mathbb T$-action in the sense that $t\cdot w\in W_0$ for every $t\in\mathbb T$ and $w\in W_0$, and let $B\colon W_0\to\operatorname{Hom}_{\mathcal O}(W_0,\mathcal O)$ be an $\mathcal O$-bilinear form on $W_0$ which is bijective as such a map (perfect), and which satisfies the following self-adjointness: for all $t\in\mathbb T$ and all $x,y,Tx,Ty\in W_0$ whose images in $V$ satisfy $Tx=t\cdot x$ and $Ty=t\cdot y$, one has $B(Tx,y)=B(x,Ty)$. Let $S$ be an idempotent splitting of $\mathbb T$, i.e. data consisting of a natural number $n$, elements $e_0,\dots,e_{n-1}\in\mathbb T$ forming a complete family of orthogonal idempotents, and maximal ideals $\mathfrak m_0,\dots,\mathfrak m_{n-1}$ of $\mathbb T$ such that every maximal ideal of $\mathbb T$ occurs among the $\mathfrak m_j$ and $e_i\in\mathfrak m_j$ exactly when $i\neq j$; fix an index $i$. Assume that the corner submodule $e_i\cdot V$ (the range of multiplication by $e_i$ on $V$) is contained in $W_0$. Then there exists a level pairing $P$ over $\mathcal O$ for the corner ring `S.CornerRing i` acting on $e_i\cdot V$ — that is, an $\mathcal O$-bilinear form $P.B$ on $e_i\cdot V$ which is perfect and for which every element of the corner ring is self-adjoint — such that $P.B(x,y)=B(x,y)$ for all $x,y\in e_i\cdot V$, the right-hand side computed by viewing $x$ and $y$ in $W_0$ via the assumed inclusion.
--
--   This is the descent of a perfect, Hecke-self-adjoint pairing on a Hecke-stable submodule to a perfect pairing on an idempotent-cut corner, self-adjoint for the corner Hecke ring; it is the self-duality input needed at each level of the tower. It is applied to the parabolic cohomology of $\Gamma_H(M)$ with its Atkin–Lehner-twisted cup product, and is used by the constructions of corner data for $H^1$ with prescribed pairing and degeneracy behaviour. Its hypothesis on $W_0$ asks only for stability of an $\mathcal O$-submodule under the $\mathbb T$-action, rather than for $W_0$ to be given as a $\mathbb T$-submodule; it is reduced to [`IharaTower.exists_levelPairing_cornerSubmodule_of_le`](thm.html#IharaTower.exists_levelPairing_cornerSubmodule_of_le), which treats the latter shape.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IharaTower_exists_levelPairing_cornerSubmodule_of_stable_of_selfAdjoint.lean

import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_HeckeModule_IharaRungDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IharaLemma IharaTower

theorem IharaTower.exists_levelPairing_cornerSubmodule_of_stable_of_selfAdjoint
    {𝒪 : Type} [CommRing 𝒪] {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋]
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module 𝕋 V] [IsScalarTower 𝒪 𝕋 V]
    (W₀ : Submodule 𝒪 V) (hstab : ∀ (t : 𝕋) (w : V), w ∈ W₀ → t • w ∈ W₀)
    (B : W₀ →ₗ[𝒪] W₀ →ₗ[𝒪] 𝒪) (hB : Function.Bijective B)
    (hadj : ∀ (t : 𝕋) (x y Tx Ty : W₀), (Tx : V) = t • (x : V) → (Ty : V) = t • (y : V) →
      B Tx y = B x Ty)
    (S : IdempotentSplitting 𝕋) (i : Fin S.n)
    (hle : ∀ v : V, v ∈ cornerSubmodule (M := V) (S.e i) → v ∈ W₀) :
    ∃ P : LevelPairing (𝒪 := 𝒪) (S.CornerRing i) ↥(cornerSubmodule (M := V) (S.e i)),
      ∀ x y : ↥(cornerSubmodule (M := V) (S.e i)),
        P.B x y = B ⟨(x : V), hle _ x.2⟩ ⟨(y : V), hle _ y.2⟩ := by sorry
