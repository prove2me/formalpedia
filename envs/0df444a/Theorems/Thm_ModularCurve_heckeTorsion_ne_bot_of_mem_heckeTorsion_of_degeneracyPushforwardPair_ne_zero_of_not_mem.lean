-- Prove2me | Theorems.Thm_ModularCurve_heckeTorsion_ne_bot_of_mem_heckeTorsion_of_degeneracyPushforwardPair_ne_zero_of_not_mem
-- name    : ModularCurve.heckeTorsion_ne_bot_of_mem_heckeTorsion_of_degeneracyPushforwardPair_ne_zero_of_not_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/d6422a20-1fd8-526f-bd68-b4ca295f6687
-- title:
--   Level-N₀ 𝔪-torsion from a p-old point when Uₚnotin𝔪
-- statement:
--   Let $N_0\ge 1$ and let $p$ be a prime with $p\nmid N_0$. Assume the input predicates `HeckeInputsAll` at level $N_0p$ and at level $N_0$ (for each prime $\ell$, the condition `HeckeInputsAlong` over $\overline{\mathbb Q}$ at that level and $\ell$), and that the operators $\mathtt{heckeOperatorBar}$ commute pairwise at both levels, so that at each of the two levels the free Hecke algebra $\mathbb T=\mathbb Z[X_\ell:\ell\text{ prime}]$ (the polynomial ring `HeckeAlg` on the set of primes) acts on the group $\mathrm{Pic}^0$ of degree-zero divisor classes $\mathrm{JZero}$ of the corresponding modular function field over $\overline{\mathbb Q}$, the variable $X_\ell$ acting as $\mathtt{heckeOperatorBar}\,\ell$. Let $\mathfrak m\subset\mathbb T$ be a maximal ideal with $p\in\mathfrak m$ and $X_p\notin\mathfrak m$, and let $x\in \mathrm{JZero}(N_0p)$ be annihilated by every element of $\mathfrak m$. Assume that at least one of the two degeneracy push-forwards $\mathrm{JZero}(N_0p)\to \mathrm{JZero}(N_0)$ of `degeneracyPushforwardPair` (the push-forwards along the two embeddings $\mathtt{heckeAlphaBar}$, $\mathtt{heckeBetaBar}$ when the degeneracy inputs hold, and $0$ otherwise) is non-zero on $x$. Then the submodule of $\mathrm{JZero}(N_0)$ annihilated by $\mathfrak m$ is non-trivial.
--
--   This is the $p$-old step in level lowering: a maximal ideal of the Hecke algebra containing $p$ and realised in the $\mathfrak m$-torsion at level $N_0p$ with $U_p$ a unit mod $\mathfrak m$ is already realised at level $N_0$, provided the point is not annihilated by both degeneracy push-forwards. It is used by [`ModularCurve.JZeroNeronObjectAtP.heckeTorsion_ne_bot_of_mem_finPts_of_not_mem_toricPts`](thm.html#ModularCurve.JZeroNeronObjectAtP.heckeTorsion_ne_bot_of_mem_finPts_of_not_mem_toricPts), where the push-forward condition is supplied by a point lying outside the toric part of the Néron fibre at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckeTorsion_ne_bot_of_mem_heckeTorsion_of_degeneracyPushforwardPair_ne_zero_of_not_mem.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_JZeroNeronAtPData
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing
  AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.heckeTorsion_ne_bot_of_mem_heckeTorsion_of_degeneracyPushforwardPair_ne_zero_of_not_mem
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (hin : HeckeInputsAll (N₀ * p)) (hcomm : HeckeOperatorsCommuteBar (N₀ * p))
    (hinN : HeckeInputsAll N₀) (hcommN : HeckeOperatorsCommuteBar N₀)
    (𝔪 : Ideal HeckeAlg) (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : ((p : ℕ) : HeckeAlg) ∈ 𝔪) (hU : heckeGen ⟨p, Fact.out⟩ ∉ 𝔪)
    (x : JZero (N₀ * p))
    (hx𝔪 : letI := heckeModuleBar (N₀ * p); x ∈ heckeTorsion (JZero (N₀ * p)) 𝔪)
    (hx : degeneracyPushforwardPair N₀ p 0 x ≠ 0 ∨ degeneracyPushforwardPair N₀ p 1 x ≠ 0) :
    letI := heckeModuleBar N₀
    heckeTorsion (JZero N₀) 𝔪 ≠ ⊥ := by sorry
