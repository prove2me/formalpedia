-- Prove2me | Theorems.Thm_ModularCurve_mem_ssPolarDifferentials_and_residue_qExpFrobeniusPlaceModL_eq_of_isFrobPushDiff
-- name    : ModularCurve.mem_ssPolarDifferentials_and_residue_qExpFrobeniusPlaceModL_eq_of_isFrobPushDiff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/93121a02-4a6f-5dd1-b652-9c96fb0d86e3
-- title:
--   Residue transport along Frobenius for q-decimating differential operators
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $p$ with $p$ prime, let $\Gamma \le \mathrm{SL}(2,\mathbb{Z})$ be of finite index with $T \in \Gamma$, and write $F =$ [`ModularCurve.qExpFunctionFieldC K Γ`](def/ModularCurve_X1.html#L101) for the intermediate field of $K((q))$ generated over $K$ by the ratios of integral $q$-expansions of modular forms of level $\Gamma$. Let $SS =$ [`ModularCurve.ssPlacesQExp K Γ p`](def/ModularCurve_XHDifferentialsModL.html#L27) be the set of places of $F/K$ satisfying the supersingularity predicate `IsSSPlaceQExp`, and let $M =$ [`ModularCurve.ssPolarDifferentials K Γ p`](def/ModularCurve_XHDifferentialsModL.html#L35) be the $K$-submodule of $\Omega[F/K]$ consisting of those $\omega$ that are regular at every place outside $SS$ and have at most a simple pole at every place in $SS$. Assume given a $K$-linear map $\mathrm{res} : M \to (\mathrm{Place}\,K\,F \to K)$ such that for every $\omega \in M$ and every $v \in SS$ the value $\mathrm{res}\,\omega\,v$ is a simple residue of $\omega$ at $v$, i.e. $\omega = f \cdot dt_v$ for some $f \in F$ with $t_v f$ having value $\mathrm{res}\,\omega\,v$ at $v$, where $t_v$ is the chosen uniformiser of $v$, and such that $\mathrm{res}\,\omega\,v = 0$ for $v \notin SS$. Assume finally given a $K$-linear endomorphism $C$ of $\Omega[F/K]$ which is a Frobenius push of differentials, namely the $q$-expansion `diffQExp` of $C\omega$ is the $p$-decimation `qDecimate` of that of $\omega$ for every $\omega$. The conclusion is twofold: $C$ maps $M$ into $M$; and for all $\omega, \omega' \in M$ with $\omega' = C\omega$ in $\Omega[F/K]$ and all $v \in SS$, one has $\mathrm{res}\,\omega'\,(\Phi v) = \mathrm{res}\,\omega\,v$, where $\Phi =$ [`ModularCurve.qExpFrobeniusPlaceModL K Γ p`](def/ModularCurve_QExpFrobeniusModL.html#L132) is the place obtained by restricting $v$ along the $K$-algebra endomorphism `qExpFrobeniusModL` of $F$.
--
--   This is the compatibility of the residue reading with the $U_p$-type operator on differentials with supersingular simple poles: the operator acting by $a_n \mapsto a_{pn}$ on $q$-expansions transports residues along the Frobenius self-map $\Phi$ of the set of supersingular places. It is used in the computations of ranks and orders attached to the corner maps on supersingular polar differentials and the associated Picard-group bookkeeping.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_mem_ssPolarDifferentials_and_residue_qExpFrobeniusPlaceModL_eq_of_isFrobPushDiff.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DifferentialPushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open AlgebraicCurve

theorem ModularCurve.mem_ssPolarDifferentials_and_residue_qExpFrobeniusPlaceModL_eq_of_isFrobPushDiff
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)

    (res : ↥(ModularCurve.ssPolarDifferentials K Γ p) →ₗ[K]
      (AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K Γ) → K))
    (hres : ∀ (ω : ↥(ModularCurve.ssPolarDifferentials K Γ p))
      (v : AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K Γ)),
      v ∈ ModularCurve.ssPlacesQExp K Γ p →
        v.HasSimpleResidue (ω : Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K]) (res ω v))
    (hres0 : ∀ (ω : ↥(ModularCurve.ssPolarDifferentials K Γ p))
      (v : AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K Γ)),
      v ∉ ModularCurve.ssPlacesQExp K Γ p → res ω v = 0)
    (C : Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K] →ₗ[K] Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K])
    (hC : ModularCurve.IsFrobPushDiff K Γ p C) :
    (∀ ω : ↥(ModularCurve.ssPolarDifferentials K Γ p),
        C (ω : Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K]) ∈ ModularCurve.ssPolarDifferentials K Γ p) ∧
    (∀ (ω ω' : ↥(ModularCurve.ssPolarDifferentials K Γ p)),
        (ω' : Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K]) = C (ω : Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K]) →
        ∀ v ∈ ModularCurve.ssPlacesQExp K Γ p,
          res ω' (ModularCurve.qExpFrobeniusPlaceModL K Γ p v) = res ω v) := by sorry
