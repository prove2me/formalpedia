-- Prove2me | Theorems.Thm_ModularCurve_hasLowerLevelTorsion_of_mem_heckeTorsion_of_degeneracyPushforwardPair_ne_zero
-- name    : ModularCurve.hasLowerLevelTorsion_of_mem_heckeTorsion_of_degeneracyPushforwardPair_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/9be0883d-d967-5de1-ba51-e15e3b0f4e2f
-- title:
--   Lower-level torsion from a non-vanishing degeneracy push-forward
-- statement:
--   Let $N_0$ and $p$ be non-zero natural numbers ($p$ is not assumed prime, nor coprime to $N_0$), and let $\mathbb{T} = \mathrm{MvPolynomial}\ \mathrm{Nat.Primes}\ \mathbb{Z}$ be the polynomial ring over $\mathbb{Z}$ on one generator `heckeGen ℓ` for each prime $\ell$. Assume the input predicates `HeckeInputsAll` at levels $N_0p$ and $N_0$, i.e. `HeckeInputsAlong (AlgebraicClosure ℚ)` holds at every prime $\ell$ for each of the two levels, and assume the commutation hypotheses `HeckeOperatorsCommuteBar` at both levels, i.e. the operators `heckeOperatorBar` at distinct primes commute on the respective degree-zero divisor class groups $\mathrm{JZero}$ over $\overline{\mathbb{Q}}$; both levels then carry the $\mathbb{T}$-module structure `heckeModuleBar`, in which `heckeGen ℓ` acts by `heckeOperatorBar`. Let $S$ be a finite set of primes containing every prime divisor of $p$, let $\mathfrak{m} \subseteq \mathbb{T}$ be an ideal, and let $x \in \mathrm{JZero}(N_0p)$ be annihilated by $\mathfrak{m}$ (membership in the submodule `heckeTorsion`, the torsion by the set $\mathfrak m$). Suppose that at least one of the two degeneracy push-forwards $\mathrm{JZero}(N_0 p) \to \mathrm{JZero}(N_0)$ packaged in `degeneracyPushforwardPair N₀ p` — push-forward along `heckeAlphaBar`, respectively `heckeBetaBar`, when the predicate `DegeneracyPushforwardInputs` holds, and the zero map otherwise — does not kill $x$. Then `HasLowerLevelTorsion S 𝔪 (JZero N₀)` holds: there exists $y \in \mathrm{JZero}(N_0)$ with $y \neq 0$, with $n \cdot y = 0$ for every natural number $n$ whose image in $\mathbb{T}$ lies in $\mathfrak{m}$, and with $(\mathrm{heckeGen}\ \ell - b) \cdot y = 0$ for every prime $\ell \notin S$ and every $b \in \mathbb{Z}$ with $\mathrm{heckeGen}\ \ell - b \in \mathfrak{m}$.
--
--   This is the $p$-old half of the transport of the support of a Hecke ideal from level $N_0p$ down to level $N_0$, as used in level lowering: an $\mathfrak{m}$-torsion point of the Jacobian at the higher level whose image under one of the two degeneracy maps is non-zero produces an $\mathfrak{m}$-torsion witness at the lower level, away from the primes in $S$. It is invoked in the case analysis of [`ModularCurve.JZeroNeronObjectAtP.hasLowerLevelTorsion_of_mem_finPts_of_not_mem_toricPts`](thm.html#ModularCurve.JZeroNeronObjectAtP.hasLowerLevelTorsion_of_mem_finPts_of_not_mem_toricPts), where the alternative case is handled by the toric/character-group argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_hasLowerLevelTorsion_of_mem_heckeTorsion_of_degeneracyPushforwardPair_ne_zero.lean

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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP
open ModularCurve

theorem ModularCurve.hasLowerLevelTorsion_of_mem_heckeTorsion_of_degeneracyPushforwardPair_ne_zero
    (N₀ p : ℕ) [NeZero N₀] [NeZero p]
    (hin : HeckeInputsAll (N₀ * p)) (hcomm : HeckeOperatorsCommuteBar (N₀ * p))
    (hinN : HeckeInputsAll N₀) (hcommN : HeckeOperatorsCommuteBar N₀)
    (S : Finset Nat.Primes) (hS : ∀ ℓ : Nat.Primes, (ℓ : ℕ) ∣ p → ℓ ∈ S)
    (𝔪 : Ideal HeckeAlg)
    (x : JZero (N₀ * p))
    (hx𝔪 : letI := heckeModuleBar (N₀ * p); x ∈ heckeTorsion (JZero (N₀ * p)) 𝔪)
    (hx : degeneracyPushforwardPair N₀ p 0 x ≠ 0 ∨ degeneracyPushforwardPair N₀ p 1 x ≠ 0) :
    letI := heckeModuleBar N₀
    HasLowerLevelTorsion S 𝔪 (JZero N₀) := by sorry
