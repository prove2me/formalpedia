-- Prove2me | Theorems.Thm_IharaTower_exists_degeneracyDescent_iDegL_jDegL_two
-- name    : IharaTower.exists_degeneracyDescent_iDegL_jDegL_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/85712308-a046-539e-8d15-425baba08b3f
-- title:
--   Two-leg degeneracy descent between levels N and Nq
-- statement:
--   Let $N$ and $q$ be nonzero naturals with $q$ prime and $q \nmid N$, let $H_s \le (\mathbb{Z}/N)^\times$ and $H_s' \le (\mathbb{Z}/Nq)^\times$, and suppose `LevelLE` holds for the pair $(N, Nq)$ with these subgroups both for $d = 1$ and for $d = q$, i.e. $N \mid Nq$, $d \mid (Nq)/N$, and reduction carries $H_s'$ into $H_s$. Let $\mathcal{O}$ be a commutative ring, $A$ an $\mathcal{O}$-module, and $\mathbb{T}$, $\mathbb{T}'$ commutative $\mathcal{O}$-algebras acting $\mathcal{O}$-compatibly on the carriers `H1 N Hs A` and `H1 (N*q) Hs' A` of additive characters of $\Gamma_{H_s}(N)$, resp. $\Gamma_{H_s'}(Nq)$, with values in $A$. Let $cd$, $cd'$ be corner data at the two levels: an idempotent splitting of the Hecke algebra, a chosen index, and a perfect self-adjoint $\mathcal{O}$-bilinear pairing on the corresponding corner submodule. Assume the two pullbacks `iDegL` along the degeneracy maps with $d = 1$ and $d = q$ carry the corner of $cd$ into the corner of $cd'$, and that the two transfers `jDegL` with $d = q$ and $d = 1$ carry the corner of $cd'$ into that of $cd$. Let $T_q$, $T_l$ be elements of the corner ring of $cd$ acting on the corner module as `heckeT N Hs q A` and `heckeTlower N Hs q A` respectively. Then there is a `DegeneracyDescent` $D$ of width $2$ with $D.\mathrm{iRaw} = (\mathrm{iDegL}_1, \mathrm{iDegL}_q)$ and $D.\mathrm{jRaw} = (\mathrm{jDegL}_q, \mathrm{jDegL}_1)$ such that for all $k, k' \in \mathrm{Fin}\,2$ and every $m$ in the corner module of $cd$, $D.\mathrm{jLeg}\,k\,(D.\mathrm{iLeg}\,k'\,m)$ equals the $(k,k')$ entry of the matrix $\begin{pmatrix} n_u T_q & n_q \\ n_1 & n_l T_l\end{pmatrix}$ applied to $m$, where $n_q$, $n_1$ are the indices in $\Gamma_{H_s}(N)$ of the images of the degeneracy maps `iotaDeg` for $d = q$, $d = 1$, while $n_u$ is the index of the image for $d = q$ inside `GammaHUpper N Hs q` and $n_l$ the index of the image for $d = 1$ inside `GammaHLower N Hs q`, each natural number being transported into the corner ring through $\mathcal{O}$.
--
--   This is the composition table for the two degeneracy legs between levels $N$ and $Nq$, in the shape required to feed an Ihara-type rung construction: the off-diagonal composites give the index multiples and the diagonal composites give index multiples of the Hecke operator at $q$ and of its lower counterpart. It is used by [`IharaTower.exists_rungDatum_two`](thm.html#IharaTower.exists_rungDatum_two) and by the construction of a Hecke-module rung at the residue characteristic with unit root.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IharaTower_exists_degeneracyDescent_iDegL_jDegL_two.lean

import Definitions.Def_CohCarrier_LevelPairing
import Definitions.Def_CohCarrier_Lower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CohCarrier IharaLemma IharaTower IharaTower.CornerData

theorem IharaTower.exists_degeneracyDescent_iDegL_jDegL_two (N q : ℕ) [NeZero N] [NeZero q]
    (hq : q.Prime) (hqN : ¬ q ∣ N) (Hs : Subgroup (ZMod N)ˣ) (Hs' : Subgroup (ZMod (N * q))ˣ)
    (h1 : LevelLE N (N * q) Hs Hs' 1) (hq' : LevelLE N (N * q) Hs Hs' q)
    {𝒪 : Type} [CommRing 𝒪] {A : Type} [AddCommGroup A] [Module 𝒪 A]
    {𝕋 𝕋' : Type} [CommRing 𝕋] [CommRing 𝕋'] [Algebra 𝒪 𝕋] [Algebra 𝒪 𝕋']
    [Module 𝕋 (H1 N Hs A)] [Module 𝕋' (H1 (N * q) Hs' A)]
    [IsScalarTower 𝒪 𝕋 (H1 N Hs A)] [IsScalarTower 𝒪 𝕋' (H1 (N * q) Hs' A)]
    (cd : H1CornerData (𝒪 := 𝒪) N Hs A 𝕋) (cd' : H1CornerData (𝒪 := 𝒪) (N * q) Hs' A 𝕋')
    (hci : ∀ (k : Fin 2) (v : H1 N Hs A), v ∈ cornerSubmodule (M := H1 N Hs A) (cd.split.e cd.idx) →
      ![iDegL N (N * q) Hs Hs' 1 A 𝒪 h1, iDegL N (N * q) Hs Hs' q A 𝒪 hq'] k v
        ∈ cornerSubmodule (M := H1 (N * q) Hs' A) (cd'.split.e cd'.idx))
    (hcj : ∀ (k : Fin 2) (v' : H1 (N * q) Hs' A),
      v' ∈ cornerSubmodule (M := H1 (N * q) Hs' A) (cd'.split.e cd'.idx) →
      ![jDegL N (N * q) Hs Hs' q A 𝒪 hq', jDegL N (N * q) Hs Hs' 1 A 𝒪 h1] k v'
        ∈ cornerSubmodule (M := H1 N Hs A) (cd.split.e cd.idx))
    (Tq Tl : cd.cornerRing)
    (hTq : ∀ m : cd.cornerModule, ((Tq • m : cd.cornerModule) : H1 N Hs A) = heckeT N Hs q A (m : H1 N Hs A))
    (hTl : ∀ m : cd.cornerModule, ((Tl • m : cd.cornerModule) : H1 N Hs A) = heckeTlower N Hs q A (m : H1 N Hs A)) :
    ∃ D : DegeneracyDescent (𝒪 := 𝒪) cd cd' 2,
      D.iRaw = ![iDegL N (N * q) Hs Hs' 1 A 𝒪 h1, iDegL N (N * q) Hs Hs' q A 𝒪 hq'] ∧
      D.jRaw = ![jDegL N (N * q) Hs Hs' q A 𝒪 hq', jDegL N (N * q) Hs Hs' 1 A 𝒪 h1] ∧
      ∀ (k k' : Fin 2) (m : cd.cornerModule), D.jLeg k (D.iLeg k' m) =
        ![![algebraMap 𝒪 cd.cornerRing (((iotaDeg N (N * q) Hs Hs' q hq').range.subgroupOf (GammaHUpper N Hs q)).index : 𝒪) * Tq,
            algebraMap 𝒪 cd.cornerRing ((iotaDeg N (N * q) Hs Hs' q hq').range.index : 𝒪)],
          ![algebraMap 𝒪 cd.cornerRing ((iotaDeg N (N * q) Hs Hs' 1 h1).range.index : 𝒪),
            algebraMap 𝒪 cd.cornerRing (((iotaDeg N (N * q) Hs Hs' 1 h1).range.subgroupOf (GammaHLower N Hs q)).index : 𝒪) * Tl]]
          k k' • m := by sorry
