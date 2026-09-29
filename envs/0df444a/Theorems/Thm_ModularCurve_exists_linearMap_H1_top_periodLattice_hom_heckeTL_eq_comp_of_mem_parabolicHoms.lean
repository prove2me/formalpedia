-- Prove2me | Theorems.Thm_ModularCurve_exists_linearMap_H1_top_periodLattice_hom_heckeTL_eq_comp_of_mem_parabolicHoms
-- name    : ModularCurve.exists_linearMap_H1_top_periodLattice_hom_heckeTL_eq_comp_of_mem_parabolicHoms
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/2fb73027-9ef2-5017-92b1-5c86d9287ceb
-- title:
--   Parabolic H¹ mod 𝔪 versus Hom(Λ_N,k), Hecke-equivariantly
-- statement:
--   Let $\mathcal O$ be a discrete valuation ring which is a domain of characteristic zero, let $k$ be a field that is an $\mathcal O$-algebra with $\mathcal O \to k$ surjective, and let $N$ be a nonzero natural number. Write $V =$ [`CohCarrier.H1 N ⊤ 𝒪`](def/CohCarrier_Level.html#L162) for the $\mathcal O$-module of additive homomorphisms $\operatorname{Additive} \Gamma \to \mathcal O$, where $\Gamma =$ [`CohCarrier.GammaH N ⊤`](def/CohCarrier_Level.html#L133) is the subgroup of $SL_2(\mathbb Z)$ obtained from $\Gamma_0(N)$ by imposing the trivial condition $\top$ on the lower-right diagonal unit, and write $V_{\mathrm{par}} \subseteq V$ for the submodule [`ModularCurve.Period.parabolicHoms`](def/ModularCurve_PeriodMap.html#L62) of those $\varphi$ vanishing on every $\gamma \in \Gamma$ whose matrix has $\operatorname{tr}(\gamma)^2 = 4$. Let $\Lambda_N =$ [`ModularCurve.periodLattice N`](def/ModularCurve_PeriodLattice.html#L102) be the $\mathbb Z$-span inside $\operatorname{Hom}_{\mathbb C}(S_2(\Gamma_0(N)),\mathbb C)$ of the periods $\gamma \mapsto$ [`ModularCurve.period N γ`](def/ModularCurve_PeriodLattice.html#L92) along paths from $i$ to $\gamma \cdot i$. The assertion is that there exists an $\mathcal O$-linear map $\Phi : V \to (\Lambda_N \to_{+} k)$ such that: (i) for every prime $\ell$ and every $v \in V_{\mathrm{par}}$, $\Phi(\mathrm{T}_\ell v) = \Phi(v) \circ \,$`periodLatticeHeckeEnd N (heckeGen ℓ)`, where $\mathrm{T}_\ell$ is the transfer operator [`CohCarrier.heckeTL N ⊤ 𝒪 ℓ`](def/CohCarrier_Inst.html#L23) (corestriction of the pullback of $\varphi$ along the conjugation map `conjL`) and the right-hand endomorphism of $\Lambda_N$ is the image of the variable indexed by $\ell$ in the polynomial Hecke algebra $\mathbb Z[X_\ell]_\ell$; (ii) $\Phi(V_{\mathrm{par}}) = \operatorname{Hom}(\Lambda_N,k)$; and (iii) for $v \in V_{\mathrm{par}}$, $\Phi(v) = 0$ if and only if $v \in \mathfrak m_{\mathcal O} V_{\mathrm{par}}$. Nothing is asserted about $\Phi$ on elements outside $V_{\mathrm{par}}$.
--
--   This is the integral Eichler–Shimura duality in the shape needed later: conditions (ii) and (iii) say that $\Phi$ induces an isomorphism $V_{\mathrm{par}} \otimes_{\mathcal O} k \cong \operatorname{Hom}(\Lambda_N,k)$, and (i) makes it compatible with the Hecke operators on parabolic classes. It is used by [`ModularCurve.exists_linearMap_H1_top_hom_torsionBy_jZero_heckeTL_eq_comp_of_mem_parabolicHoms`](thm.html#ModularCurve.exists_linearMap_H1_top_hom_torsionBy_jZero_heckeTL_eq_comp_of_mem_parabolicHoms), which cuts the construction down to a Hecke eigencomponent.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_linearMap_H1_top_periodLattice_hom_heckeTL_eq_comp_of_mem_parabolicHoms.lean

import Mathlib
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_ModularCurve_PeriodLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.exists_linearMap_H1_top_periodLattice_hom_heckeTL_eq_comp_of_mem_parabolicHoms
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [CharZero 𝒪]
    {k : Type} [Field k] [Algebra 𝒪 k] (hk : Function.Surjective (algebraMap 𝒪 k))
    (N : ℕ) [NeZero N] :
    ∃ Φ : CohCarrier.H1 N ⊤ 𝒪 →ₗ[𝒪] (↥(ModularCurve.periodLattice N) →+ k),
      (∀ (ℓ : Nat.Primes) (v : CohCarrier.H1 N ⊤ 𝒪),
        v ∈ ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH N ⊤) 𝒪 →
          Φ ((haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩; CohCarrier.heckeTL N ⊤ 𝒪 ℓ) v) =
            (Φ v).comp
              (ModularCurve.periodLatticeHeckeEnd N (ModularCurve.heckeGen ℓ)).toAddMonoidHom) ∧
      (ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH N ⊤) 𝒪).map Φ = ⊤ ∧
      (∀ v : CohCarrier.H1 N ⊤ 𝒪,
        v ∈ ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH N ⊤) 𝒪 →
          (Φ v = 0 ↔ v ∈ IsLocalRing.maximalIdeal 𝒪 •
            ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH N ⊤) 𝒪)) := by sorry
