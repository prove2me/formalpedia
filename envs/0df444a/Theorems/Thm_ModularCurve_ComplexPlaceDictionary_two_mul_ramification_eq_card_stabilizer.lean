-- Prove2me | Theorems.Thm_ModularCurve_ComplexPlaceDictionary_two_mul_ramification_eq_card_stabilizer
-- name    : ModularCurve.ComplexPlaceDictionary.two_mul_ramification_eq_card_stabilizer
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/4e0beeaf-997c-5764-a273-13c525c5eb4f
-- title:
--   Doubled ramification equals stabiliser order in Γ₀(N)
-- statement:
--   Let $N$ be a nonzero natural number, and let $\mathbb{C}F_N$ denote the intermediate field `laurentBaseChange ℂ (modularFunctionFieldFull N)` of $\mathbb{C}((q))$, generated over $\mathbb{C}$ by the image, under the coefficientwise embedding, of the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the divisor expansions at level $N$. Let $D$ be a complex place dictionary at level $N$: a family of places $P_\tau = D.\mathrm{pt}(\tau)$ of $\mathbb{C}F_N$ over $\mathbb{C}$ (each a valuation subring, proper, containing $\mathbb{C}$ and a principal ideal ring) together with positive integers $e_\tau = D.\mathrm{ramification}(\tau)$, indexed by $\tau$ in the upper half plane, such that $P_{\gamma\tau} = P_\tau$ for $\gamma \in \Gamma_0(N)$; such that $x \in \mathbb{C}F_N$ lies in the valuation ring of $P_\tau$ exactly when $z \mapsto \lVert \mathrm{realize}\,N\,x\,(z)\rVert$ is bounded on a punctured neighbourhood of $\tau$; and such that for $x \neq 0$ the meromorphic order at $z = \tau$ of $z \mapsto \mathrm{realize}\,N\,x$ equals $e_\tau \cdot \operatorname{ord}_{P_\tau}(x)$. Here $\mathrm{realize}\,N\,x\,(\tau)$ is $g(\tau)/h(\tau)$ for some pair $g,h$ of modular forms of equal weight on $\Gamma_0(N)$ with $h(\tau) \neq 0$ and $x \cdot \widetilde{h} = \widetilde{g}$ on $q$-expansions, and $0$ if no such pair exists. Then for every $\tau$ in the upper half plane, $2e_\tau$ equals the cardinality of the stabiliser of $\tau$ in $\Gamma_0(N)$.
--
--   This identifies the abstractly axiomatised integer $e_\tau$ with the ramification index of the quotient map $\mathfrak{H} \to \Gamma_0(N)\backslash\mathfrak{H}$ at $\tau$, i.e. with the order of the stabiliser of $\tau$ in $\Gamma_0(N)/\{\pm 1\}$, the stabiliser in $\mathrm{SL}_2(\mathbb{Z})$ always containing $-1$. It is used in the analytic comparisons attached to the dictionary, notably in the statements on Abel–Jacobi images of divisors of prescribed order and on the Hecke action on single places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ComplexPlaceDictionary_two_mul_ramification_eq_card_stabilizer.lean

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

theorem ModularCurve.ComplexPlaceDictionary.two_mul_ramification_eq_card_stabilizer
    {N : ℕ} [NeZero N] (D : ModularCurve.ComplexPlaceDictionary N) (τ : UpperHalfPlane) :
    2 * D.ramification τ =
      Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ) := by sorry
