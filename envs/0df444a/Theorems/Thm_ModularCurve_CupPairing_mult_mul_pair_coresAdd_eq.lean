-- Prove2me | Theorems.Thm_ModularCurve_CupPairing_mult_mul_pair_coresAdd_eq
-- name    : ModularCurve.CupPairing.mult_mul_pair_coresAdd_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/0a90f2b8-011c-5ee9-b75a-95813973f0c2
-- title:
--   Projection formula for corestriction and the cup pairing
-- statement:
--   Let $\Gamma$ be a finite-index subgroup of $\mathrm{SL}_2(\mathbb Z)$ and let $K$ be a finite-index subgroup of $\Gamma$; write $\Gamma' =$ `K.map Γ.subtype` for the image of $K$ inside $\mathrm{SL}_2(\mathbb Z)$. Let $x$ be an additive homomorphism from $\Gamma$ (written additively) to $\mathbb Q$, let $xK$ and $y'$ be such homomorphisms on $\Gamma'$, and let $yK$ be such a homomorphism on $K$. Assume $x$ and $y'$ are parabolic in the sense of [`ModularCurve.Period.IsParabolicHom`](def/ModularCurve_PeriodMap.html#L15), i.e. they vanish on every element whose matrix has trace squared equal to $4$; assume further that $xK$ is the transport of $x$ along the isomorphism $K \to \Gamma'$, $k \mapsto k$, and that $yK$ is the transport of $y'$ back along the same isomorphism. Then $$m_\Gamma \cdot \langle x, \mathrm{cores}_K(yK)\rangle_\Gamma = m_{\Gamma'} \cdot \langle xK, y'\rangle_{\Gamma'},$$ where $\mathrm{cores}_K$ is [`CohCarrier.coresAdd`](def/CohCarrier_Level.html#L63), the additive form of the group-theoretic transfer from $K$ to $\Gamma$, $m_\Gamma = 1$ if $-1 \in \Gamma$ and $m_\Gamma = 2$ otherwise, and $\langle \varphi, \psi\rangle_\Gamma$ denotes [`ModularCurve.CupPairing.pair`](def/ModularCurve_CupPairing.html#L18): for a finite-index $\Gamma$ admitting a function $h : \Gamma \to \mathbb Q$ with $h(gg') = h(g) + h(g') - \omega_{\varphi,\psi}(g,g')$ for the $2$-cocycle $\omega_{\varphi,\psi} =$ [`ModularCurve.PDPairing.omega φ ψ`](def/ModularCurve_PDPairing.html#L386), it is the sum of a chosen such $h$ over the cusp generators [`ModularCurve.PDPairing.cuspGen`](def/ModularCurve_PDPairing.html#L570), divided by $2m_\Gamma$, and $0$ when no such $h$ exists.
--
--   This is the projection formula (adjointness of corestriction and restriction) for the cup pairing on parabolic cohomology, in the form $\langle x, \pi_!y'\rangle = \langle \pi^*x, y'\rangle$ for the covering of modular curves attached to $K \le \Gamma$, with the factors $m_\Gamma$, $m_{\Gamma'}$ recording the difference between the group-cohomological transfer and the Gysin map. It is used in comparing the pairing under conjugation of subgroups and in the computation of the pairing against Hecke, diamond and Fricke operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CupPairing_mult_mul_pair_coresAdd_eq.lean

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_CupPairing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.CupPairing.mult_mul_pair_coresAdd_eq (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (K : Subgroup Γ) [K.FiniteIndex]
    (x : Additive Γ →+ ℚ) (xK y' : Additive (K.map Γ.subtype) →+ ℚ) (yK : Additive K →+ ℚ)
    (hx : ModularCurve.Period.IsParabolicHom Γ x)
    (hy' : ModularCurve.Period.IsParabolicHom (K.map Γ.subtype) y')
    (hxK : ∀ k : K, xK (Additive.ofMul ⟨((k : Γ) : SL(2, ℤ)), Subgroup.mem_map_of_mem Γ.subtype k.2⟩) =
      x (Additive.ofMul (k : Γ)))
    (hyK : ∀ k : K, yK (Additive.ofMul k) =
      y' (Additive.ofMul ⟨((k : Γ) : SL(2, ℤ)), Subgroup.mem_map_of_mem Γ.subtype k.2⟩)) :
    ModularCurve.CupPairing.mult Γ * ModularCurve.CupPairing.pair Γ x (CohCarrier.coresAdd K yK) =
      ModularCurve.CupPairing.mult (K.map Γ.subtype) *
        ModularCurve.CupPairing.pair (K.map Γ.subtype) xK y' := by sorry
