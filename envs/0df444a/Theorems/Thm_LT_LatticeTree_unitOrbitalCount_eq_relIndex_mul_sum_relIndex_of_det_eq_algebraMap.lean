-- Prove2me | Theorems.Thm_LT_LatticeTree_unitOrbitalCount_eq_relIndex_mul_sum_relIndex_of_det_eq_algebraMap
-- name    : LT.LatticeTree.unitOrbitalCount_eq_relIndex_mul_sum_relIndex_of_det_eq_algebraMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/c1c61851-2f31-5642-a92a-3331feded7af
-- title:
--   Fixed vertices of a unit-determinant class as a weighted double-coset count
-- statement:
--   Let $K$ be a number field, $v$ a nonzero prime of $\mathcal{O}_K$, with completion $K_v$ and valuation ring $\mathcal{O}_v$; let $\gamma \in \mathrm{GL}_2(K_v)$ and $u \in \mathcal{O}_v^{\times}$ with $\det \gamma$ equal to the image of $u$ under $\mathcal{O}_v \to K_v$. Write $T =$ the centraliser of $\{\gamma\}$ in $\mathrm{GL}_2(K_v)$ and $U =$ [`AutomorphicForm.localIntegralSet K v`](def/AutomorphicForm_LocalOrbitalBase.html#L100), the set of $g \in \mathrm{GL}_2(K_v)$ such that both $g$ and $g^{-1}$ have all entries in $\mathcal{O}_v$. Assume given: a subgroup $T_c$ whose elements are exactly the $t \in T$ with $\det t$ in the image of $\mathcal{O}_v^{\times}$; a family of subgroups $T_s$, indexed by $s \in \mathrm{GL}_2(K_v)$, whose elements are exactly the $t \in T$ with $s^{-1} t s \in U$; and a finite set $S$ of elements $s$ with $s^{-1}\gamma s \in U$, such that any two members of $S$ lying in a common double coset $T s U$ coincide, and every $x$ with $x^{-1}\gamma x \in U$ lies in $T s U$ for some $s \in S$. Then [`LT.LatticeTree.unitOrbitalCount`](def/LatticeTreeOrbital.html#L1442) of $\gamma$ over $\mathcal{O}_v$, that is the cardinality (as a natural number, $0$ if infinite) of the set of vertices $w$ of [`LT.LatticeTree.Vertex`](def/LatticeTreeOrbital.html#L349) over $\mathcal{O}_v \subseteq K_v$ satisfying the predicate `IsFixedVertex` for $\gamma$, equals the index of $(T_c \vee Z) \cap T$ in $T$, where $Z$ is the centre of $\mathrm{GL}_2(K_v)$, times $\sum_{s \in S}$ of the index of $T_s \cap T_c$ in $T_c$.
--
--   This is the local counting identity at a finite place of a number field: the number of vertices of the Bruhat–Tits tree of $\mathrm{GL}_2(K_v)$ fixed by an element of integral unit determinant is expressed as an index-weighted count over a system of representatives for the double cosets $T \backslash \{x : x^{-1}\gamma x \in \mathrm{GL}_2(\mathcal{O}_v)\} / \mathrm{GL}_2(\mathcal{O}_v)$, the weights being the masses occurring in the orbital integral of the indicator function of $\mathrm{GL}_2(\mathcal{O}_v)$. It is used in the local computation of orbital integrals and in the construction of matching Hecke operators at inert primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LT_LatticeTree_unitOrbitalCount_eq_relIndex_mul_sum_relIndex_of_det_eq_algebraMap.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LatticeTreeOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem
LT.LatticeTree.unitOrbitalCount_eq_relIndex_mul_sum_relIndex_of_det_eq_algebraMap
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (γ : GL (Fin 2) (v.adicCompletion K)) (u : (v.adicCompletionIntegers K)ˣ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u)
    (Tc : Subgroup (GL (Fin 2) (v.adicCompletion K)))
    (hTc : ∀ t : GL (Fin 2) (v.adicCompletion K),
      t ∈ Tc ↔ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) ∧
        ∃ w : (v.adicCompletionIntegers K)ˣ,
          Matrix.det (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
            algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) w)
    (St : GL (Fin 2) (v.adicCompletion K) → Subgroup (GL (Fin 2) (v.adicCompletion K)))
    (hSt : ∀ s t : GL (Fin 2) (v.adicCompletion K),
      t ∈ St s ↔ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) ∧
        s⁻¹ * t * s ∈ AutomorphicForm.localIntegralSet K v)
    (S : Finset (GL (Fin 2) (v.adicCompletion K)))
    (hSsupp : ∀ s ∈ S, s⁻¹ * γ * s ∈ AutomorphicForm.localIntegralSet K v)
    (hS :
      ∀ s ∈ S, ∀ s' ∈ S,
        ∀ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))),
          ∀ u ∈ AutomorphicForm.localIntegralSet K v, s' = t * s * u → s' = s)
    (hcov :
      ∀ x : GL (Fin 2) (v.adicCompletion K), x⁻¹ * γ * x ∈ AutomorphicForm.localIntegralSet K v →
        ∃ s ∈ S,
          ∃ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))),
            ∃ u ∈ AutomorphicForm.localIntegralSet K v, x = t * s * u) :
    LT.LatticeTree.unitOrbitalCount (v.adicCompletionIntegers K) γ =
      (Tc ⊔ Subgroup.center (GL (Fin 2) (v.adicCompletion K))).relIndex
          (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) *
        ∑ s ∈ S, (St s).relIndex Tc := by sorry
