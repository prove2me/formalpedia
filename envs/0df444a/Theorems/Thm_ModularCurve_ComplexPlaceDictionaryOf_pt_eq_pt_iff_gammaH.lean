-- Prove2me | Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_pt_eq_pt_iff_gammaH
-- name    : ModularCurve.ComplexPlaceDictionaryOf.pt_eq_pt_iff_gammaH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/f9568f42-dc06-50f7-8558-580a0f9f653d
-- title:
--   Places of X_H(M) separate Γ_H(M)-orbits on H
-- statement:
--   Fix $M \in \mathbb{N}$ with $M \neq 0$ and a subgroup $H \leq (\mathbb{Z}/M)^{\times}$, and write $\Gamma_H(M)$ for the subgroup [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}_2(\mathbb{Z})$, namely the image in $\mathrm{SL}_2(\mathbb{Z})$ of those $\gamma \in \Gamma_0(M)$ whose lower-right entry reduces modulo $M$ to a unit lying in $H$ (the relevant homomorphism [`CohCarrier.gamma0Units`](def/CohCarrier_Level.html#L121) sends $\gamma$ to the unit $d \bmod M$, with inverse $a \bmod M$). Let $F_0$ be the intermediate field [`ModularCurve.xHFunctionField M H`](def/ModularCurve_XH.html#L79) of $\mathbb{Q} \subseteq \mathbb{Q}((q))$ attached to level $\Gamma_H(M)$, and let $D$ be a complex place dictionary for the pair $(\Gamma_H(M), F_0)$: thus $D$ consists of a map $\mathrm{pt}$ from the upper half-plane $\mathfrak{H}$ to the places of $\mathbb{C}F_0 =$ `laurentBaseChange ℂ F₀` (the subfield of $\mathbb{C}((q))$ generated over $\mathbb{C}$ by the coefficientwise image of $F_0$) over $\mathbb{C}$, together with a strictly positive ramification index $e(\tau)$, such that $\mathrm{pt}$ is invariant under the action of $\Gamma_H(M)$ on $\mathfrak{H}$, such that $x \in \mathbb{C}F_0$ lies in the valuation subring of $\mathrm{pt}(\tau)$ exactly when $z \mapsto \lVert \mathrm{realizeOf}\,\Gamma_H(M)\,x\,z\rVert$ is bounded along the punctured neighbourhood filter of $\tau$, and such that for $x \neq 0$ the meromorphic order at $\tau$ of the realisation of $x$ equals $e(\tau) \cdot \mathrm{ord}_{\mathrm{pt}(\tau)}(x)$; here $\mathrm{realizeOf}\,\Gamma\,x\,\tau$ is $g(\tau)/h(\tau)$ for a chosen pair of modular forms $g,h$ of a common weight on $\Gamma$ with $h(\tau) \neq 0$ and $x$ times the $q$-expansion of $h$ equal to that of $g$ (and $0$ if no such pair exists). Then for all $\tau, \tau' \in \mathfrak{H}$ one has $\mathrm{pt}(\tau) = \mathrm{pt}(\tau')$ if and only if $\gamma \cdot \tau = \tau'$ for some $\gamma \in \Gamma_H(M)$.
--
--   This is the injectivity statement underlying the identification of the open modular curve $Y_H(M) = \Gamma_H(M) \backslash \mathfrak{H}$ with a set of places of the function field of $X_H(M)$: the forward implication is the content, the converse being the invariance clause of the dictionary. It is used in the comparison of divisors and Abel–Jacobi data on $X_H(M)$ with points of $\mathfrak{H}$, for instance by [`ModularCurve.ComplexPlaceDictionaryOf.heckeDivHBar_single_pt`](thm.html#ModularCurve.ComplexPlaceDictionaryOf.heckeDivHBar_single_pt) and by the statements relating the Abel–Jacobi map and the period lattice at level $\Gamma_H(M)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ComplexPlaceDictionaryOf_pt_eq_pt_iff_gammaH.lean

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_XH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.ComplexPlaceDictionaryOf.pt_eq_pt_iff_gammaH (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ)
    (D : ModularCurve.ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (ModularCurve.xHFunctionField M H))
    (τ τ' : UpperHalfPlane) :
    D.pt τ = D.pt τ' ↔ ∃ γ ∈ CohCarrier.GammaH M H, γ • τ = τ' := by sorry
