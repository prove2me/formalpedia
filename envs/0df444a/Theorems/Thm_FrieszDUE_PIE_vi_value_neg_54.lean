-- Prove2me | Theorems.Thm_FrieszDUE_PIE_vi_value_neg_54
-- name    : FrieszDUE.PIE.vi_value_neg_54
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:19:53.139659+00:00
-- url     : https://prove2.me/theorems/57b1ba1f-945f-4de4-b160-61e4cd577482
-- title:
--   (51)–(54), pp. 188–189 — at the shifted h, Σ_p ∫ C_p(t, h*)[h_p − h*_p] dν ≤ −εδα
-- statement:
--   In the setting of the PIE model, let $h^*$ be a density vector whose costs $C_r(\cdot,h^*)$ are square-integrable on $[0,T]$, write $\mu^*_{kl}=\mu_{kl}(h^*)$, let $p\ne q$ be paths of the same OD pair $kl$, and let $\varepsilon,\delta,\alpha>0$. Let $A,B$ be measurable sets with $\nu(A)=\nu(B)=\alpha$ such that
--
--   $$C_p(t,h^*)>\mu^*_{kl}+2\varepsilon\quad\forall_\nu(t\in A),\qquad C_q(t,h^*)<\mu^*_{kl}+\varepsilon\quad\forall_\nu(t\in B).$$
--
--   If $h$ is obtained from $h^*$ by the mass shift (48)–(49) ($\delta$ removed from path $p$ on $A$, added to path $q$ on $B$), then
--
--   $$\sum_{r\in P}\int_0^T C_r(t,h^*)\,[h_r(t)-h^*_r(t)]\,d\nu(t)\le-\varepsilon\delta\alpha.\qquad(54)$$
--
--   Together with the feasibility (50) of $h$, this contradicts (39) and closes the sufficiency half of Theorem 2.
-- source:
--   Friesz, Bernstein, Smith, Tobin and Wie, A variational inequality formulation of the dynamic network user equilibrium problem, Oper. Res. 41 (1993), pp. 188–189, proof of Theorem 2 part ii, (51)–(54)

import Mathlib
import Definitions.Def_FrieszDUE_PIE_Setting

namespace FrieszDUE.PIE

open MeasureTheory

/-- Proof of Theorem 2 part ii, (51)–(54), pp. 188–189. -/
theorem vi_value_neg_54 {P W : Type*} [Fintype P] [DecidableEq P] [DecidableEq W]
    (T : ℝ) (od : P → W) (C : P → ℝ → (P → ℝ → ℝ) → ℝ) (hs : P → ℝ → ℝ)
    (hC_L2 : ∀ p, MemLp (fun t => C p t hs) 2 (ν T))
    (p q : P) (hpq : p ≠ q) (hod : od p = od q) (ε δ α : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (hα : 0 < α) (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAα : ν T A = ENNReal.ofReal α) (hBα : ν T B = ENNReal.ofReal α)
    (hCA : ∀ᵐ t ∂(ν T), t ∈ A → muOD T od C hs (od p) + 2 * ε < C p t hs)
    (hCB : ∀ᵐ t ∂(ν T), t ∈ B → C q t hs < muOD T od C hs (od p) + ε) :
    ∑ r, ∫ t, C r t hs * (massShift hs p q A B δ r t - hs r t) ∂(ν T) ≤ -ε * δ * α := by sorry

end FrieszDUE.PIE
