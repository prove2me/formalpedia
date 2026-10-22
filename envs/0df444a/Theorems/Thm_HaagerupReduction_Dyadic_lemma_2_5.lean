-- Prove2me | Theorems.Thm_HaagerupReduction_Dyadic_lemma_2_5
-- name    : HaagerupReduction.Dyadic.lemma_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:28:13.285642+00:00
-- url     : https://prove2.me/theorems/f23b1a3a-5155-411c-abbe-d1601789f1ea
-- title:
--   Lemma 2.5, p. 9 — for a normal faithful state ψ: x analytic ⇒ xψx* ≤ cψ; x in the centralizer N_ψ ⇒ xψx* ≤ ‖x‖²ψ
-- statement:
--   Let $N$ be a von Neumann algebra on a Hilbert space $K$ in standard form with a normal faithful state $\psi(y) = \langle y\xi_0,\xi_0\rangle$ (unit cyclic separating vector $\xi_0$) and modular group $\sigma^\psi_t(y) = \Delta^{it}y\Delta^{-it}$. For $x\in N$ write $x\psi x^*$ for the functional $y\mapsto\psi(x^*yx)$. Let $x\in N$.
--
--   1. If $x$ is analytic, i.e. $t\mapsto\sigma^\psi_t(x)$ extends to an entire function $\mathbb C\to B(K)$, then there is a constant $c\ge0$ with
--   $$\psi(x^*yx)\le c\,\psi(y)\qquad\text{for all } y\in N,\ y\ge0.$$
--   2. If $x\in N_\psi$, i.e. $\sigma^\psi_t(x) = x$ for all $t\in\mathbb R$, then
--   $$\psi(x^*yx)\le\|x\|^2\,\psi(y)\qquad\text{for all } y\in N,\ y\ge0.$$
--
--   The lemma lets the $\hat\varphi$-seminorm of a commutator $[y,x]$ be bounded by $\|y\|_{\hat\varphi}$ in Lemma 2.6.
--
--   **Formalization Note.** $(N,\psi)$ is given by the published standard-form encoding `StandardModularData`; every von Neumann algebra with a normal faithful state is spatially isomorphic to one of these. Both sides are real for $y\ge0$; the inequalities compare real parts. The paper's definition of analytic element writes "$F_x:\mathbb C\to\mathcal M$", which means $\mathbb C\to N$; holomorphy here is in operator norm (weakly entire functions are norm entire).
-- source:
--   Haagerup, Junge & Xu, A reduction method for noncommutative Lp-spaces and applications, arXiv:0806.3635v2, p. 9, Lemma 2.5 (analytic elements defined just before it; aψb(y) = ψ(bya) from p. 7)

import Mathlib
import Definitions.Def_BoundedRecovery
import Definitions.Def_HaagerupReduction_Dyadic_Model

namespace HaagerupReduction.Dyadic

universe u

open OAI.BoundedRecovery
open Filter Topology

/-- Lemma 2.5, for a von Neumann algebra `N = T.M` in standard form with the normal faithful
state `ψ = vstate T`: (i) analytic `x` gives `x ψ x^* ≤ c ψ` for some `c ≥ 0`; (ii) `x` in the
centralizer gives `x ψ x^* ≤ ‖x‖² ψ`. Here `(x ψ x^*)(y) = ψ(x^* y x)`. -/
theorem lemma_2_5 {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (T : StandardModularData H) (x : H →L[ℂ] H) (hx : x ∈ T.M) :
    (IsAnalytic T x → ∃ c : ℝ, 0 ≤ c ∧
      ∀ y ∈ T.M, 0 ≤ y → (vstate T (star x * y * x)).re ≤ c * (vstate T y).re) ∧
    ((∀ t : ℝ, T.sigma t x = x) →
      ∀ y ∈ T.M, 0 ≤ y → (vstate T (star x * y * x)).re ≤ ‖x‖ ^ 2 * (vstate T y).re) := by sorry

end HaagerupReduction.Dyadic
