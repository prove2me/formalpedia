-- Prove2me | Theorems.Thm_IharaTower_CornerData_exists_orthogonal_stable_complement_of_corner_le_of_selfAdjoint
-- name    : IharaTower.CornerData.exists_orthogonal_stable_complement_of_corner_le_of_selfAdjoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/88cc1b5c-f40c-5eb9-960b-47e41147dc48
-- title:
--   Stable orthogonal complement of a refinement corner
-- statement:
--   Let $\mathcal O$ be a commutative ring, let $\mathbb T_a$ and $\mathbb T_1$ be commutative $\mathcal O$-algebras, and let $V$ be an abelian group carrying compatible module structures over $\mathcal O$, $\mathbb T_a$ and $\mathbb T_1$ (scalar towers over $\mathcal O$). Let $\iota\colon\mathbb T_a\to\mathbb T_1$ be an $\mathcal O$-algebra map with $\iota(t)\cdot v=t\cdot v$ for all $t\in\mathbb T_a$, $v\in V$. Let $cd_a$ be a corner datum for $\mathbb T_a$ on $V$: an idempotent splitting of $\mathbb T_a$ (a complete orthogonal family of idempotents $e_i$ together with maximal ideals $\mathfrak m_i$ exhausting the maximal ideals of $\mathbb T_a$ and satisfying $e_i\in\mathfrak m_j\iff i\neq j$), a distinguished index with idempotent $e_a$, and a level pairing over $\mathcal O$ on the corner module $e_aV=\operatorname{range}(e_a\cdot\mathrm{id}_V)$, that is an $\mathcal O$-bilinear form $B$ which is bijective as a map into the $\mathcal O$-dual and self-adjoint for the corner ring of $e_a$. Let $S_1$ be an idempotent splitting of $\mathbb T_1$ with a chosen index, idempotent $e_1$, assume $e_1V\subseteq e_aV$, and assume that every $t\in\mathbb T_1$ is self-adjoint for $B$, in the form: whenever $x,y,Tx,Ty$ lie in $e_aV$ with $Tx=t\cdot x$ and $Ty=t\cdot y$ in $V$, one has $B(Tx,y)=B(x,Ty)$. Then there is an $\mathcal O$-submodule $C\subseteq V$ such that $v\in e_aV$ holds exactly when $v=v_1+v_2$ with $v_1\in e_1V$ and $v_2\in C$; any $v$ lying in both $e_1V$ and $C$ is $0$; for $x,y\in e_aV$ with $x\in e_1V$ and $y\in C$ one has $B(x,y)=B(y,x)=0$; and $C$ is stable under the corner ring of $e_a$ acting on $e_aV$.
--
--   This is the ordinary (unit-root) refinement step in the form used for corner data: the local component of a cohomology carrier at the smaller Hecke algebra decomposes as the component cut out by a finer idempotent plus a complement which is both $B$-orthogonal to it and stable under the corner ring. It is invoked in the construction of the refined $H^1$ corner datum along a degeneracy map raising the level, for a corner datum with full corner under the trace and non-divisibility hypotheses there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IharaTower_CornerData_exists_orthogonal_stable_complement_of_corner_le_of_selfAdjoint.lean

import Definitions.Def_CohCarrier_LevelPairing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IharaTower.CornerData.exists_orthogonal_stable_complement_of_corner_le_of_selfAdjoint
    {𝒪 : Type} [CommRing 𝒪]
    {𝕋ₐ 𝕋₁ : Type} [CommRing 𝕋ₐ] [CommRing 𝕋₁] [Algebra 𝒪 𝕋ₐ] [Algebra 𝒪 𝕋₁]
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module 𝕋ₐ V] [Module 𝕋₁ V]
    [IsScalarTower 𝒪 𝕋ₐ V] [IsScalarTower 𝒪 𝕋₁ V]
    (ι : 𝕋ₐ →ₐ[𝒪] 𝕋₁) (hι : ∀ (t : 𝕋ₐ) (v : V), ι t • v = t • v)
    (cdₐ : IharaTower.CornerData (𝒪 := 𝒪) 𝕋ₐ V) (S₁ : IharaLemma.IdempotentSplitting 𝕋₁) (i₁ : Fin S₁.n)
    (hincl : ∀ v : V, v ∈ IharaLemma.cornerSubmodule (M := V) (S₁.e i₁) →
      v ∈ IharaLemma.cornerSubmodule (M := V) (cdₐ.split.e cdₐ.idx))
    (hadj : ∀ (t : 𝕋₁) (x y Tx Ty : cdₐ.cornerModule), (Tx : V) = t • (x : V) → (Ty : V) = t • (y : V) →
      cdₐ.pairing.B Tx y = cdₐ.pairing.B x Ty) :
    ∃ C : Submodule 𝒪 V,
      (∀ v : V, v ∈ IharaLemma.cornerSubmodule (M := V) (cdₐ.split.e cdₐ.idx) ↔
        ∃ v₁ v₂, v₁ ∈ IharaLemma.cornerSubmodule (M := V) (S₁.e i₁) ∧ v₂ ∈ C ∧ v = v₁ + v₂) ∧
      (∀ v, v ∈ IharaLemma.cornerSubmodule (M := V) (S₁.e i₁) → v ∈ C → v = 0) ∧
      (∀ (x y : cdₐ.cornerModule), (x : V) ∈ IharaLemma.cornerSubmodule (M := V) (S₁.e i₁) → (y : V) ∈ C →
        cdₐ.pairing.B x y = 0 ∧ cdₐ.pairing.B y x = 0) ∧
      (∀ (t : cdₐ.cornerRing) (y : cdₐ.cornerModule), (y : V) ∈ C →
        ((t • y : cdₐ.cornerModule) : V) ∈ C) := by sorry
