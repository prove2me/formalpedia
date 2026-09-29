-- Prove2me | Theorems.Thm_LT_LatticeTree_card_orbitalBall_sdiff_eq_relIndex_mul_sum_relIndex_of_det_eq_mul_zpow
-- name    : LT.LatticeTree.card_orbitalBall_sdiff_eq_relIndex_mul_sum_relIndex_of_det_eq_mul_zpow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/aeb0107b-80db-53d1-99a7-627cbcdbbf37
-- title:
--   Vertices moved distance exactly n counted by double cosets
-- statement:
--   Let $K$ be a number field, $v$ a finite place of $K$, i.e. a height-one prime of $\mathcal O_K$, and write $\mathcal O_v$ for the integers of the completion $K_v$. Let $\varpi\in\mathcal O_v$ be irreducible, $\gamma\in \mathrm{GL}_2(K_v)$, $b\in\mathbb Z$, $n\ge 1$ and $u\in\mathcal O_v^{\times}$, and assume $\det\gamma=u\,\varpi^{2b+n}$ (images under $\mathcal O_v\to K_v$). Let $dl\in\mathrm{GL}_2(K_v)$ have matrix $\mathrm{diagonal}(\varpi^{b+n},\varpi^{b})$, and write $U$ for [`AutomorphicForm.localIntegralSet K v`](def/AutomorphicForm_LocalOrbitalBase.html#L100), the set of $g\in\mathrm{GL}_2(K_v)$ such that both $g$ and $g^{-1}$ have all entries in $\mathcal O_v$, and $T$ for the centraliser of $\{\gamma\}$. Let $T_c$ be a subgroup characterised by: $t\in T_c$ iff $t\in T$ and $\det t$ lies in the image of $\mathcal O_v^{\times}$; and for each $s$ let $T_s$ be a subgroup characterised by: $t\in T_s$ iff $t\in T$ and $s^{-1}ts\in U$. Let $S$ be a finite set of elements $s$ with $s^{-1}\gamma s\in U\cdot\{dl\}\cdot U$, pairwise inequivalent in the sense that $s'=t s u$ with $t\in T$, $u\in U$ and $s,s'\in S$ forces $s'=s$, and such that every $x$ with $x^{-1}\gamma x\in U\cdot\{dl\}\cdot U$ is of the form $t s u$ with $s\in S$, $t\in T$, $u\in U$. Then the number of homothety classes of full $\mathcal O_v$-lattices in $K_v^2$ (vertices) lying in [`LT.LatticeTree.orbitalBall`](def/LatticeTreeBaseChange.html#L392) of radius $n$ for $\gamma$ and the unit $\varpi\in K_v^{\times}$ but not in that of radius $n-1$ — that is, vertices $x$ for which the pair $(x,\gamma x)$ satisfies the relation `LatticeWithin` at parameter $n$ but not at $n-1$ — is finite and equals the relative index of $T_c\cdot Z$ in $T$, where $Z$ is the centre of $\mathrm{GL}_2(K_v)$, times $\sum_{s\in S}$ of the relative index of $T_s$ in $T_c$.
--
--   This is the local counting identity behind orbital integrals on the Bruhat–Tits tree of $\mathrm{GL}_2(K_v)$: the mass of vertices displaced by exactly $n$ by a class $\gamma$ of determinant valuation $2b+n$ is expressed as an index-weighted count over representatives of the double cosets $T s U$ meeting the Hecke double coset $U\,\mathrm{diag}(\varpi^{b+n},\varpi^{b})\,U$. It is used in the comparison of orbital integrals with tree-theoretic shadows and in the construction of matching Hecke operators at inert primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LT_LatticeTree_card_orbitalBall_sdiff_eq_relIndex_mul_sum_relIndex_of_det_eq_mul_zpow.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LatticeTreeBaseChange
import Mathlib.Algebra.Group.Pointwise.Set.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Pointwise

theorem
LT.LatticeTree.card_orbitalBall_sdiff_eq_relIndex_mul_sum_relIndex_of_det_eq_mul_zpow
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) (γ : GL (Fin 2) (v.adicCompletion K))
    (b : ℤ) (n : ℕ) (hn : 1 ≤ n) (u : (v.adicCompletionIntegers K)ˣ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ (2 * b + (n : ℤ)))
    (dl : GL (Fin 2) (v.adicCompletion K))
    (hdl : (dl : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      Matrix.diagonal
        ![algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ (b + (n : ℤ)),
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ b])
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
    (hSsupp : ∀ s ∈ S,
      s⁻¹ * γ * s ∈
        AutomorphicForm.localIntegralSet K v *
            ({dl} : Set (GL (Fin 2) (v.adicCompletion K))) *
          AutomorphicForm.localIntegralSet K v)
    (hS :
      ∀ s ∈ S, ∀ s' ∈ S,
        ∀ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))),
          ∀ u ∈ AutomorphicForm.localIntegralSet K v, s' = t * s * u → s' = s)
    (hcov :
      ∀ x : GL (Fin 2) (v.adicCompletion K),
        x⁻¹ * γ * x ∈
          AutomorphicForm.localIntegralSet K v *
              ({dl} : Set (GL (Fin 2) (v.adicCompletion K))) *
            AutomorphicForm.localIntegralSet K v →
        ∃ s ∈ S,
          ∃ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))),
            ∃ u ∈ AutomorphicForm.localIntegralSet K v, x = t * s * u) :
    Nat.card
        ↥(LT.LatticeTree.orbitalBall (R := v.adicCompletionIntegers K)
            (LT.LatticeTree.unitOfNeZero (K := v.adicCompletion K) hϖ.ne_zero) n γ \
          LT.LatticeTree.orbitalBall (R := v.adicCompletionIntegers K)
            (LT.LatticeTree.unitOfNeZero (K := v.adicCompletion K) hϖ.ne_zero) (n - 1) γ) =
      (Tc ⊔ Subgroup.center (GL (Fin 2) (v.adicCompletion K))).relIndex
          (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) *
        ∑ s ∈ S, (St s).relIndex Tc := by sorry
