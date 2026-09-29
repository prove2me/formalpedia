-- Prove2me | Theorems.Thm_ModularCurve_ComplexPlaceDictionary_pt_eq_pt_iff
-- name    : ModularCurve.ComplexPlaceDictionary.pt_eq_pt_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/27ab4180-d780-5585-974e-d43bb5410757
-- title:
--   Places of a dictionary coincide iff Γ₀(N)-equivalent
-- statement:
--   Fix $N \ge 1$ and write $\mathbb{C}F_N$ for the intermediate field [`ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)`](def/ModularCurve_LaurentCoeff.html#L103) of $\mathbb{C}((q))$, namely the field generated over $\mathbb{C}$ by the coefficientwise images of the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the $q$-expansions `divisorExpansions N`. Let $D$ be a [`ModularCurve.ComplexPlaceDictionary N`](def/ModularCurve_ComplexPlaceDictionary.html#L28), that is: a map $\tau \mapsto D.\mathrm{pt}\,\tau$ from the upper half plane $\mathfrak{H}$ to places of $\mathbb{C}F_N$ over $\mathbb{C}$ (a valuation subring of $\mathbb{C}F_N$ containing the image of $\mathbb{C}$, not equal to the whole field, and a principal ideal ring), together with positive integers $D.\mathrm{ramification}\,\tau$, subject to: $D.\mathrm{pt}(\gamma \cdot \tau) = D.\mathrm{pt}\,\tau$ for all $\gamma \in \Gamma_0(N)$; an element $x \in \mathbb{C}F_N$ lies in the valuation subring of $D.\mathrm{pt}\,\tau$ exactly when $z \mapsto \|\mathrm{realize}\,N\,x\,z\|$ is bounded above along the punctured neighbourhood filter of $\tau$, where $\mathrm{realize}\,N\,x$ is the function $g/h$ attached to some presentation $x \cdot \tilde h = \tilde g$ with $g, h$ modular forms of a common weight on $\Gamma_0(N)$, $h(\tau) \ne 0$ (and $0$ if no such presentation exists); and, for $x \ne 0$, the meromorphic order at $\tau$ of $z \mapsto \mathrm{realize}\,N\,x\,(\mathrm{ofComplex}\,z)$ equals $D.\mathrm{ramification}\,\tau$ times $\mathrm{ord}_{D.\mathrm{pt}\,\tau}(x)$. Then for all $\tau, \tau' \in \mathfrak{H}$, one has $D.\mathrm{pt}\,\tau = D.\mathrm{pt}\,\tau'$ if and only if $\gamma \cdot \tau = \tau'$ for some $\gamma \in \Gamma_0(N)$.
--
--   This is the injectivity on non-cuspidal points of the map from $\Gamma_0(N)\backslash\mathfrak{H}$ to the places of the function field of $X_0(N)$: the meromorphic functions $g/h$ with $g,h$ modular forms of equal weight on $\Gamma_0(N)$ separate $\Gamma_0(N)$-orbits. It is used throughout the dictionary between analytic points of $\mathfrak{H}$ and divisors on $X_0(N)$, for instance in the computation of Hecke operators on divisors supported at single points and in the Abel–Jacobi statements attached to a place dictionary.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ComplexPlaceDictionary_pt_eq_pt_iff.lean

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane in
open scoped MatrixGroups in

theorem ModularCurve.ComplexPlaceDictionary.pt_eq_pt_iff {N : ℕ} [NeZero N]
    (D : ModularCurve.ComplexPlaceDictionary N) (τ τ' : ℍ) :
    D.pt τ = D.pt τ' ↔ ∃ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • τ = τ' := by sorry
