-- Prove2me | Theorems.Thm_IharaTower_jDegL_heckeT_eq_unitRoot_smul_of_ordinary_refinement
-- name    : IharaTower.jDegL_heckeT_eq_unitRoot_smul_of_ordinary_refinement
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/61895a4d-5391-53b5-b3fb-c6c5f15bde8b
-- title:
--   Degeneracy traces intertwine U_q with the unit root
-- statement:
--   Fix nonzero naturals $N,q$ (with $Nq$ nonzero), a subgroup $H_s\le(\mathbb Z/N)^\times$ and a subgroup $H_s'\le(\mathbb Z/Nq)^\times$, together with two instances `LevelLE` of degrees $1$ and $q$, each asserting $N\mid Nq$, that the degree divides $(Nq)/N$, and that reduction of units carries $H_s'$ into $H_s$. Let $\mathcal O$ be a noetherian local commutative ring; for a level $M$ and group $H$ write $H^1(M,H,\mathcal O)$ for the $\mathcal O$-module `H1` of additive homomorphisms $\mathrm{Additive}\,\Gamma_H(M)\to\mathcal O$, equipped with the transfer operators `heckeT` and with the $\mathcal O$-linear degeneracy traces $j_d=$ `jDegL` from level $Nq$ to level $N$ for $d\in\{1,q\}$. Let $\mathbb T,\mathbb T_a,\mathbb T_1$ be commutative $\mathcal O$-algebras, $\mathbb T$ acting on $H^1(N,H_s,\mathcal O)$ and $\mathbb T_a,\mathbb T_1$ on $H^1(Nq,H_s',\mathcal O)$ compatibly with $\mathcal O$, and let $cd,cd_a,cd_1$ be corner data for them: an idempotent splitting, an index, and a level pairing on the associated corner ring and corner submodule $\mathrm{range}(e\cdot\mathrm{id})$. Assume: every element of $\mathbb T_1$ preserves the corner submodule $e_a H^1(Nq,H_s',\mathcal O)$ cut out by $cd_a$; both $j_q$ and $j_1$ map that submodule into the corner submodule $eH^1(N,H_s,\mathcal O)$ cut out by $cd$; $U\in\mathbb T_1$ acts on all of $H^1(Nq,H_s',\mathcal O)$ as `heckeT` of degree $q$; elements $t_p,\tilde\alpha$ of the corner ring of $cd$ satisfy $\tilde\alpha^2-t_p\tilde\alpha+q=0$ and $t_p-\tilde\alpha\in\mathfrak m$, with $t_p$ acting on the corner module as `heckeT` of degree $q$ at level $N$; on the $cd_a$-corner submodule the relations $j_1(U_qv')=q\,j_q(v')$ and $j_q(U_qv')=T_q(j_q v')-j_1(v')$ hold; the corner module and corner ring of $cd$ are finite over $\mathcal O$; and $U$ lies outside the maximal ideal attached to the index of $cd_1$. Then for every $v'$ lying in both the $cd_a$- and the $cd_1$-corner submodules of $H^1(Nq,H_s',\mathcal O)$, and every pair $jm_q,jm_1$ of corner-module elements whose underlying classes are $j_q(v')$ and $j_1(v')$, one has $j_q(U_qv')=\tilde\alpha\cdot jm_q$ and $j_1(U_qv')=\tilde\alpha\cdot jm_1$ in $H^1(N,H_s,\mathcal O)$.
--
--   This is the Hecke-module form of the statement that on an ordinary (unit-root) component at level $Nq$ the degeneracy traces carry the action of $U_q$ to multiplication by the unit root $\tilde\alpha$ of $X^2-T_qX+q$, the other root $t_p-\tilde\alpha$ being a non-unit of the corner ring. It is used in the construction of corner-data refinements at level $Nq$ from corner data at level $N$, and in the comparison of the degeneracy traces with the corner-ring scalar action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IharaTower_jDegL_heckeT_eq_unitRoot_smul_of_ordinary_refinement.lean

import Definitions.Def_CohCarrier_LevelPairing
import Mathlib.RingTheory.Noetherian.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CohCarrier IharaLemma IharaTower

theorem IharaTower.jDegL_heckeT_eq_unitRoot_smul_of_ordinary_refinement
    {N q : ℕ} [NeZero N] [NeZero q] [NeZero (N * q)]
    {Hs : Subgroup (ZMod N)ˣ} {Hs' : Subgroup (ZMod (N * q))ˣ}
    (h1 : LevelLE N (N * q) Hs Hs' 1) (hq' : LevelLE N (N * q) Hs Hs' q)
    {𝒪 : Type} [CommRing 𝒪] [IsNoetherianRing 𝒪] [IsLocalRing 𝒪]
    {𝕋 𝕋ₐ 𝕋₁ : Type} [CommRing 𝕋] [CommRing 𝕋ₐ] [CommRing 𝕋₁] [Algebra 𝒪 𝕋] [Algebra 𝒪 𝕋ₐ] [Algebra 𝒪 𝕋₁]
    [Module 𝕋 (H1 N Hs 𝒪)] [Module 𝕋ₐ (H1 (N * q) Hs' 𝒪)] [Module 𝕋₁ (H1 (N * q) Hs' 𝒪)]
    [IsScalarTower 𝒪 𝕋 (H1 N Hs 𝒪)] [IsScalarTower 𝒪 𝕋ₐ (H1 (N * q) Hs' 𝒪)] [IsScalarTower 𝒪 𝕋₁ (H1 (N * q) Hs' 𝒪)]
    (cd : H1CornerData (𝒪 := 𝒪) N Hs 𝒪 𝕋) (cdₐ : H1CornerData (𝒪 := 𝒪) (N * q) Hs' 𝒪 𝕋ₐ)
    (cd₁ : H1CornerData (𝒪 := 𝒪) (N * q) Hs' 𝒪 𝕋₁)
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
    (v' : H1 (N * q) Hs' 𝒪)
    (hva : v' ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cdₐ.split.e cdₐ.idx))
    (hv1 : v' ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cd₁.split.e cd₁.idx))
    (jmq jm1 : cd.cornerModule)
    (hjmq : (jmq : H1 N Hs 𝒪) = jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' v')
    (hjm1 : (jm1 : H1 N Hs 𝒪) = jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 v') :
    jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' (heckeT (N * q) Hs' q 𝒪 v') = ((αt • jmq : cd.cornerModule) : H1 N Hs 𝒪) ∧
    jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 (heckeT (N * q) Hs' q 𝒪 v') = ((αt • jm1 : cd.cornerModule) : H1 N Hs 𝒪) := by sorry
