-- Prove2me | Theorems.Thm_ModularCurve_CupPairing_exists_isPrimitive
-- name    : ModularCurve.CupPairing.exists_isPrimitive
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/67b0f188-9410-569f-9504-cb226402d957
-- title:
--   Antisymmetrised cup product of rational characters has a primitive
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb{Z})$ of finite index, and let $\varphi, \psi$ be two homomorphisms from the additive group underlying $\Gamma$ (that is, $\Gamma$ regarded through `Additive` as an additive group) to $\mathbb{Q}$; thus $\varphi$ and $\psi$ are rational characters of $\Gamma$, satisfying $\varphi(gg') = \varphi(g) + \varphi(g')$ and likewise for $\psi$. The assertion is that there exists a function $h \colon \Gamma \to \mathbb{Q}$ which is a primitive of the antisymmetrised product of $\varphi$ and $\psi$, in the sense that for all $g, g' \in \Gamma$ one has
--   $$h(gg') = h(g) + h(g') - \bigl(\varphi(g)\psi(g') - \psi(g)\varphi(g')\bigr),$$
--   the subtracted term being the $2$-cochain $\omega(g,g')$ attached to the pair $(\varphi,\psi)$. Equivalently, the $2$-cocycle $\omega$ is a coboundary: $h$ exhibits it as the difference $h(g) + h(g') - h(gg')$. No continuity, parity or normalisation condition is imposed on $h$, and $h$ is not asserted to be unique.
--
--   This is the vanishing of the class of $\varphi \cup \psi - \psi \cup \varphi$ in $H^2(\Gamma, \mathbb{Q})$ for a finite-index subgroup $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$, obtained from the freeness of $\Gamma(4)$ ([`ModularCurve.PDPairing.isFreeGroup_Gamma_four`](thm.html#ModularCurve.PDPairing.isFreeGroup_Gamma_four)) together with the fact that corestriction after restriction is multiplication by the index, invertible on $\mathbb{Q}$. The existence of such a primitive is used in the construction and comparison of the pairings on the cohomology of modular curves, in particular in the Hecke- and Fricke-compatibility statements and in the production of a perfect antisymmetric pairing on a corner submodule of $H^1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CupPairing_exists_isPrimitive.lean

import Mathlib
import Definitions.Def_ModularCurve_CupPairing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.CupPairing.exists_isPrimitive (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (φ ψ : Additive Γ →+ ℚ) :
    ∃ h : Γ → ℚ, ModularCurve.CupPairing.IsPrimitive φ ψ h := by sorry
