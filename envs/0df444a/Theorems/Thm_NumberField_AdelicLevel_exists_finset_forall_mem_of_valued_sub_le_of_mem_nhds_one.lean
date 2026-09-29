-- Prove2me | Theorems.Thm_NumberField_AdelicLevel_exists_finset_forall_mem_of_valued_sub_le_of_mem_nhds_one
-- name    : NumberField.AdelicLevel.exists_finset_forall_mem_of_valued_sub_le_of_mem_nhds_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/8c609aef-a185-58c6-be69-3e2c7d756b1c
-- title:
--   Principal congruence subgroups are a neighbourhood basis at 1
-- statement:
--   Let $K$ be a number field with ring of integers $\mathcal O_K$, and let $V$ be a subset of $\mathrm{GL}_2(\mathbb A_K)$, where $\mathbb A_K$ is the adele ring of $K$, which is a neighbourhood of the identity matrix. Then there exist a finite set $T$ of height-one primes of $\mathcal O_K$ and a natural number $e$ such that every $g \in \mathrm{GL}_2(\mathbb A_K)$ satisfying the following three conditions lies in $V$: first, the image of $g$ under the map $\mathrm{GL}_2(\mathbb A_K) \to \mathrm{GL}_2(\mathbb A_{K,\infty})$ induced by the projection $\mathbb A_K \to \mathbb A_{K,\infty}$ onto the infinite-adelic component is the identity; second, for every height-one prime $v$ and all $i,j \in \{0,1\}$, the $v$-component of the finite-adelic part of the $(i,j)$ entry of $g$, and likewise of $g^{-1}$, lies in the valuation ring of the completion $K_v$; third, for every $v \in T$ and all $i,j$, the $v$-components of the entries of $g$ and of $g^{-1}$ satisfy $\mathrm{v}\bigl(g_{ij} - \delta_{ij}\bigr) \le \exp(-e)$ in the value group $\mathbb Z^{\mathrm{m}0}$ of $K_v$, written multiplicatively.
--
--   This is the standard description of the topology of $\mathrm{GL}_2$ of the adeles near the identity: the principal congruence subgroups of level $(T,e)$, intersected with the matrices integral at all finite places and with trivial archimedean component, form a fundamental system of neighbourhoods of $1$ in the finite-adelic direction. It is the device that converts openness of a stabiliser into invariance under a congruence subgroup of some finite level, and it is used in the construction of smooth vectors and test functions for adelic automorphic forms, for instance in the results on factorisable test functions and on local zeta integrals of Godement sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicLevel_exists_finset_forall_mem_of_valued_sub_le_of_mem_nhds_one.lean

import Mathlib
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped Topology

theorem NumberField.AdelicLevel.exists_finset_forall_mem_of_valued_sub_le_of_mem_nhds_one
    (K : Type) [Field K] [NumberField K]
    (V : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))) (_hV : V ∈ 𝓝 (1 : GL (Fin 2) (AdeleRing (𝓞 K) K))) :
    ∃ (T : Finset (HeightOneSpectrum (𝓞 K))) (e : ℕ),
      ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K), glArch (𝓞 K) K g = 1 →
        (∀ (v : HeightOneSpectrum (𝓞 K)) (i j : Fin 2),
          ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v ∈ v.adicCompletionIntegers K ∧
          (((g⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v
            ∈ v.adicCompletionIntegers K) →
        (∀ v ∈ T, ∀ i j : Fin 2,
          Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v
              - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ WithZero.exp (-(e : ℤ)) ∧
          Valued.v ((((g⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v
              - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ WithZero.exp (-(e : ℤ))) →
        g ∈ V := by sorry
