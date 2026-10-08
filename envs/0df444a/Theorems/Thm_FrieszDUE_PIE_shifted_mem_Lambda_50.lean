-- Prove2me | Theorems.Thm_FrieszDUE_PIE_shifted_mem_Lambda_50
-- name    : FrieszDUE.PIE.shifted_mem_Lambda_50
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:19:57.794899+00:00
-- url     : https://prove2.me/theorems/5e72bfa8-975a-44d9-b152-48570e860069
-- title:
--   (48)–(50), p. 188 — moving δ units of flow from p on A to q on B, ν(A) = ν(B), keeps the densities in Λ
-- statement:
--   In the setting of the PIE model, let $h^*\in\Lambda$, let $p\ne q$ be two paths of the same OD pair $kl$, let $\delta>0$, and let $A,B$ be measurable sets with $\nu(A)=\nu(B)$ such that $h^*_p(t)\ge\delta$ for $\nu$-almost all $t\in A$. Define $h$ by (48)–(49):
--
--   $$h_p(t)=\begin{cases}h^*_p(t)-\delta,& t\in A\\ h^*_p(t),& t\notin A\end{cases}\qquad h_q(t)=\begin{cases}h^*_q(t)+\delta,& t\in B\\ h^*_q(t),& t\notin B\end{cases}$$
--
--   and $h_r=h^*_r$ for every other path $r$. Then $h\in\Lambda$.
--
--   In the paper $A=S_p(\varepsilon,\delta,\alpha)$ and $B=T_q(\varepsilon,\alpha)$ both have measure $\alpha$; the demand identity (50) shows the shifted vector is feasible.
--
--   **Formalization Note** The paper reduces the case $p=q$ to $p\ne q$ (p. 188); the statement takes $p\ne q$ as a hypothesis.
-- source:
--   Friesz, Bernstein, Smith, Tobin and Wie, A variational inequality formulation of the dynamic network user equilibrium problem, Oper. Res. 41 (1993), p. 188, proof of Theorem 2 part ii, (48)–(50)

import Mathlib
import Definitions.Def_FrieszDUE_PIE_Setting

namespace FrieszDUE.PIE

open MeasureTheory

/-- Proof of Theorem 2 part ii, (48)–(50), p. 188. -/
theorem shifted_mem_Lambda_50 {P W : Type*} [Fintype P] [DecidableEq P] [DecidableEq W]
    (T : ℝ) (od : P → W) (Q : W → ℝ) (hs : P → ℝ → ℝ) (hhs : hs ∈ Lambda T od Q)
    (p q : P) (hpq : p ≠ q) (hod : od p = od q) (δ : ℝ) (hδ : 0 < δ)
    (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : ν T A = ν T B)
    (hδA : ∀ᵐ t ∂(ν T), t ∈ A → δ ≤ hs p t) :
    massShift hs p q A B δ ∈ Lambda T od Q := by sorry

end FrieszDUE.PIE
