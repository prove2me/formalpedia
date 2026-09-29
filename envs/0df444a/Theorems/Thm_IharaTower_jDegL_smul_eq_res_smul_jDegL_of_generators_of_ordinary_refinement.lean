-- Prove2me | Theorems.Thm_IharaTower_jDegL_smul_eq_res_smul_jDegL_of_generators_of_ordinary_refinement
-- name    : IharaTower.jDegL_smul_eq_res_smul_jDegL_of_generators_of_ordinary_refinement
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/e0114c2a-f98e-5c74-a875-1379eee45360
-- title:
--   Res-equivariance of the degeneracy traces on the ordinary corner
-- statement:
--   Fix naturals $N,q$ (with $N$, $q$, $Nq$ nonzero), subgroups $H_s\le(\mathbb Z/N)^\times$, $H_s'\le(\mathbb Z/Nq)^\times$, and two `LevelLE` data $h_1$, $h_{q}$ for the pair $(N,Nq)$ with degrees $1$ and $q$, each asserting $N\mid Nq$, that the degree divides $(Nq)/N$, and that reduction carries $H_s'$ into $H_s$. Let $\mathcal O$ be a noetherian local commutative ring and $\mathbb T,\mathbb T_a,\mathbb T_1$ commutative $\mathcal O$-algebras acting $\mathcal O$-compatibly on the carriers $H^1(\Gamma_{H_s}(N),\mathcal O)$, resp. $H^1(\Gamma_{H_s'}(Nq),\mathcal O)$ (groups of additive maps on the relevant congruence subgroup), with corner data $cd$, $cd_a$, $cd_1$, each consisting of an idempotent splitting of the algebra, an index, and a level pairing on the corresponding corner ring and corner submodule $e\cdot H^1$. Assume: the $cd_1$-corner is contained in the $cd_a$-corner; the $cd_a$-corner is stable under $\mathbb T_1$; both traces `jDegL` of degrees $q$ and $1$ send the $cd_a$-corner into the $cd$-corner; $U\in\mathbb T_1$ acts on $H^1(\Gamma_{H_s'}(Nq),\mathcal O)$ as `heckeT` at $q$; elements $t_p,\alpha_t$ of $cd$'s corner ring satisfy $\alpha_t^2-t_p\alpha_t+q=0$, with $t_p$ acting on the $cd$-corner module as `heckeT` at $q$ and $t_p-\alpha_t$ in the maximal ideal; the relations $j_1(U\,v')=q\,j_q(v')$ and $j_q(U\,v')=T_q\,j_q(v')-j_1(v')$ hold on the $cd_a$-corner; the $cd$-corner module and corner ring are finite over $\mathcal O$; $U$ lies outside the ideal `cd₁.split.𝔪` at the index of $cd_1$; $res$ is an $\mathcal O$-algebra map from $cd_1$'s to $cd$'s corner ring with $res$ of the corner image of $U$ equal to $\alpha_t$; and $G$ generates $cd_1$'s corner ring as an $\mathcal O$-algebra, each $x\in G$ being either that corner image of $U$ or equipped with set maps $A'$ on the upper and $A$ on the lower carrier through which $x$, resp. $res\,x$, act on the respective corner modules and which are intertwined by both traces on the $cd_1$-corner. Then for every $t_1$ in $cd_1$'s corner ring, every $m'$ in its corner module, and all $jm,jtm$ in $cd$'s corner module whose underlying classes are the degree-$q$ trace of $m'$ and of $t_1\cdot m'$, one has $jtm=res(t_1)\cdot jm$; and the same with the degree-$1$ trace throughout.
--
--   This is the compatibility of the level-lowering algebra map on the ordinary part at level $Nq$ (sending Hecke operators to Hecke operators and $U_q$ to the unit root $\alpha_t$ of $X^2-T_qX+q$) with both degeneracy trace maps to level $N$: equivariance checked on algebra generators propagates to the whole corner ring. It feeds the construction of refined corner data at level $Nq$ used in the Ihara-type comparison of Hecke modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IharaTower_jDegL_smul_eq_res_smul_jDegL_of_generators_of_ordinary_refinement.lean

import Definitions.Def_CohCarrier_LevelPairing
import Mathlib.RingTheory.Noetherian.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CohCarrier IharaLemma IharaTower

theorem IharaTower.jDegL_smul_eq_res_smul_jDegL_of_generators_of_ordinary_refinement
    {N q : ℕ} [NeZero N] [NeZero q] [NeZero (N * q)]
    {Hs : Subgroup (ZMod N)ˣ} {Hs' : Subgroup (ZMod (N * q))ˣ}
    (h1 : LevelLE N (N * q) Hs Hs' 1) (hq' : LevelLE N (N * q) Hs Hs' q)
    {𝒪 : Type} [CommRing 𝒪] [IsNoetherianRing 𝒪] [IsLocalRing 𝒪]
    {𝕋 𝕋ₐ 𝕋₁ : Type} [CommRing 𝕋] [CommRing 𝕋ₐ] [CommRing 𝕋₁] [Algebra 𝒪 𝕋] [Algebra 𝒪 𝕋ₐ] [Algebra 𝒪 𝕋₁]
    [Module 𝕋 (H1 N Hs 𝒪)] [Module 𝕋ₐ (H1 (N * q) Hs' 𝒪)] [Module 𝕋₁ (H1 (N * q) Hs' 𝒪)]
    [IsScalarTower 𝒪 𝕋 (H1 N Hs 𝒪)] [IsScalarTower 𝒪 𝕋ₐ (H1 (N * q) Hs' 𝒪)] [IsScalarTower 𝒪 𝕋₁ (H1 (N * q) Hs' 𝒪)]
    (cd : H1CornerData (𝒪 := 𝒪) N Hs 𝒪 𝕋) (cdₐ : H1CornerData (𝒪 := 𝒪) (N * q) Hs' 𝒪 𝕋ₐ)
    (cd₁ : H1CornerData (𝒪 := 𝒪) (N * q) Hs' 𝒪 𝕋₁)
    (hincl : ∀ v : H1 (N * q) Hs' 𝒪, v ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cd₁.split.e cd₁.idx) →
      v ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cdₐ.split.e cdₐ.idx))
    (hstab : ∀ (t : 𝕋₁) (v : H1 (N * q) Hs' 𝒪),
      v ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cdₐ.split.e cdₐ.idx) →
      t • v ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cdₐ.split.e cdₐ.idx))
    (mjq : ∀ v' : H1 (N * q) Hs' 𝒪, v' ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cdₐ.split.e cdₐ.idx) →
      jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' v' ∈ cornerSubmodule (M := H1 N Hs 𝒪) (cd.split.e cd.idx))
    (mj1 : ∀ v' : H1 (N * q) Hs' 𝒪, v' ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cdₐ.split.e cdₐ.idx) →
      jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 v' ∈ cornerSubmodule (M := H1 N Hs 𝒪) (cd.split.e cd.idx))
    (U : 𝕋₁) (hUact : ∀ v' : H1 (N * q) Hs' 𝒪, U • v' = heckeT (N * q) Hs' q 𝒪 v')
    (tp αt : cd.cornerRing)
    (hquad : αt * αt - tp * αt + algebraMap 𝒪 cd.cornerRing (q : 𝒪) = 0)
    (hTp : ∀ m : cd.cornerModule, ((tp • m : cd.cornerModule) : H1 N Hs 𝒪) = heckeT N Hs q 𝒪 (m : H1 N Hs 𝒪))
    (R1 : ∀ v' : H1 (N * q) Hs' 𝒪, v' ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cdₐ.split.e cdₐ.idx) →
      jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 (heckeT (N * q) Hs' q 𝒪 v') = q • jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' v')
    (R2 : ∀ v' : H1 (N * q) Hs' 𝒪, v' ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cdₐ.split.e cdₐ.idx) →
      jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' (heckeT (N * q) Hs' q 𝒪 v') =
        heckeT N Hs q 𝒪 (jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' v') - jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 v')
    [Module.Finite 𝒪 cd.cornerModule] [Module.Finite 𝒪 cd.cornerRing]
    (hUunit : U ∉ cd₁.split.𝔪 cd₁.idx)
    (hβmem : tp - αt ∈ IsLocalRing.maximalIdeal cd.cornerRing)
    (res : cd₁.cornerRing →ₐ[𝒪] cd.cornerRing)
    (hresU : res (cd₁.split.toCornerRing cd₁.idx U) = αt)
    (G : Set cd₁.cornerRing) (hG : Algebra.adjoin 𝒪 G = ⊤)
    (hgen : ∀ x ∈ G,
      (∃ (A' : H1 (N * q) Hs' 𝒪 → H1 (N * q) Hs' 𝒪) (A : H1 N Hs 𝒪 → H1 N Hs 𝒪),
        (∀ m : cd₁.cornerModule, ((x • m : cd₁.cornerModule) : H1 (N * q) Hs' 𝒪) =
          A' (m : H1 (N * q) Hs' 𝒪)) ∧
        (∀ m : cd.cornerModule, ((res x • m : cd.cornerModule) : H1 N Hs 𝒪) = A (m : H1 N Hs 𝒪)) ∧
        (∀ v' : H1 (N * q) Hs' 𝒪, v' ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cd₁.split.e cd₁.idx) →
          jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' (A' v') = A (jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' v')) ∧
        (∀ v' : H1 (N * q) Hs' 𝒪, v' ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cd₁.split.e cd₁.idx) →
          jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 (A' v') = A (jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 v'))) ∨
      x = cd₁.split.toCornerRing cd₁.idx U) :
    (∀ (t₁ : cd₁.cornerRing) (m' : cd₁.cornerModule) (jm jtm : cd.cornerModule),
      (jm : H1 N Hs 𝒪) = jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' (m' : H1 (N * q) Hs' 𝒪) →
      (jtm : H1 N Hs 𝒪) = jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' ((t₁ • m' : cd₁.cornerModule) : H1 (N * q) Hs' 𝒪) →
      jtm = res t₁ • jm) ∧
    (∀ (t₁ : cd₁.cornerRing) (m' : cd₁.cornerModule) (jm jtm : cd.cornerModule),
      (jm : H1 N Hs 𝒪) = jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 (m' : H1 (N * q) Hs' 𝒪) →
      (jtm : H1 N Hs 𝒪) = jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 ((t₁ • m' : cd₁.cornerModule) : H1 (N * q) Hs' 𝒪) →
      jtm = res t₁ • jm) := by sorry
