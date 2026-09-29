-- Prove2me | Theorems.Thm_IharaTower_exists_levelPairing_cornerSubmodule_of_le
-- name    : IharaTower.exists_levelPairing_cornerSubmodule_of_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/85573e03-fcd8-56b1-9781-7928d8200813
-- title:
--   Restricting a perfect self-adjoint pairing to an idempotent corner
-- statement:
--   Let $\mathcal O$ be a commutative ring, $\mathbb T$ a commutative $\mathcal O$-algebra, and $V$ an abelian group carrying compatible $\mathcal O$- and $\mathbb T$-module structures (a scalar tower). Let $W$ be a $\mathbb T$-submodule of $V$, and let $B \colon W \to W \to \mathcal O$ be an $\mathcal O$-bilinear form which is perfect in the sense that the induced map $W \to \operatorname{Hom}_{\mathcal O}(W,\mathcal O)$, $x \mapsto B(x,\cdot)$, is bijective, and for which every $t \in \mathbb T$ is self-adjoint: $B(t \cdot x, y) = B(x, t \cdot y)$ for all $x,y \in W$. Let $S$ be an idempotent splitting of $\mathbb T$, that is, data consisting of an integer $n$, elements $e_0,\dots,e_{n-1}$ of $\mathbb T$ forming a complete orthogonal family of idempotents, and maximal ideals $\mathfrak m_0,\dots,\mathfrak m_{n-1}$ exhausting all maximal ideals of $\mathbb T$ and satisfying $e_i \in \mathfrak m_j \iff i \neq j$. Fix an index $i$ and put $e = e_i$; let the corner submodule be the image $e \cdot V \subseteq V$ of multiplication by $e$ on $V$, and assume it is contained in $W$. The assertion is that there exists a level pairing $P$ on $e \cdot V$ over the corner ring of the idempotent $e$ — an $\mathcal O$-bilinear form on $e \cdot V$ that is perfect in the above sense and for which every element of the corner ring is self-adjoint — whose underlying form is the restriction of $B$: $P(x,y) = B(x,y)$ for all $x,y \in e \cdot V$, the right-hand side being computed after the inclusion of $e \cdot V$ into $W$.
--
--   This is the bookkeeping step that transports a perfect, Hecke-self-adjoint pairing on a global Hecke module (for instance a cup-product pairing on the cohomology of a modular curve) to the localisation at one maximal ideal of the Hecke algebra, producing the self-dual pairing required at each rung of a Taylor–Wiles tower. It is used in the construction of refined corner data for degeneracy maps at multiplied level, and in the variant that also records stability and self-adjointness hypotheses.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IharaTower_exists_levelPairing_cornerSubmodule_of_le.lean

import Definitions.Def_HeckeModule_IharaRungDatum
import Definitions.Def_IharaLemma_IdempotentSplitting

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem IharaTower.exists_levelPairing_cornerSubmodule_of_le
    {𝒪 : Type} [CommRing 𝒪] {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋]
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module 𝕋 V] [IsScalarTower 𝒪 𝕋 V]
    (W : Submodule 𝕋 V) (B : W →ₗ[𝒪] W →ₗ[𝒪] 𝒪) (hB : Function.Bijective B)
    (hadj : ∀ (t : 𝕋) (x y : W), B (t • x) y = B x (t • y))
    (S : IharaLemma.IdempotentSplitting 𝕋) (i : Fin S.n)
    (hle : IharaLemma.cornerSubmodule (M := V) (S.e i) ≤ W) :
    ∃ P : IharaTower.LevelPairing (𝒪 := 𝒪) (S.CornerRing i)
        ↥(IharaLemma.cornerSubmodule (M := V) (S.e i)),
      ∀ x y : ↥(IharaLemma.cornerSubmodule (M := V) (S.e i)),
        P.B x y = B (Submodule.inclusion hle x) (Submodule.inclusion hle y) := by sorry
