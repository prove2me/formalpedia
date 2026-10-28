-- Prove2me | Theorems.Thm_GroupBuyEq_Signup_boundary_i
-- name    : GroupBuyEq.Signup.boundary_i
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T09:20:27.281546+00:00
-- url     : https://prove2.me/theorems/217d58fa-758d-41fb-bc3e-3ecf91413991
-- title:
--   Boundary condition (i), p. 8 — π¹_k(T) = 0 for k < M₁ and π²_k(T) = 0 for k < M₂ in equilibrium
-- statement:
--   In the two-threshold group-buying model under the standing assumptions, let $(\pi^1_k,\pi^2_k)_{k\ge0}$ be a dynamic consumer equilibrium for a probability law $\mu$ of the reservation utility. Then at the closing time $T$ of the event,
--   $$\pi^1_k(T)=0\quad\text{for }0\le k<M_1,\qquad \pi^2_k(T)=0\quad\text{for }0\le k<M_2 .$$
--
--   If the event closes with fewer than $M_1$ (resp. $M_2$) sign-ups, the first (resp. second) deal cannot happen. The paper lists this as boundary condition (i) and uses it in the proof of Proposition 1 at (A.13).
--
--   **Formalization Note** In the formalization the equilibrium is defined by the conditioning equations (4) and (5), and (i) is their value at $t=T$, so it is stated as a consequence rather than imposed.
-- source:
--   Ming & Tunca, Consumer Equilibrium, Demand Effects, and Efficiency in Group Buying, SSRN 3352047 (version of 2020-05-15), p. 8 (PDF 9), §3.2, boundary condition (i)

import Mathlib
import Definitions.Def_GroupBuyEq_Signup_Model

namespace GroupBuyEq.Signup

theorem boundary_i (P : Params) (hP : P.Standing) (μ : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure μ] (E : Profile) (hE : IsEquilibrium P μ E) :
    (∀ k : ℕ, k < P.M1 → E.pi1 k P.T = 0) ∧ (∀ k : ℕ, k < P.M2 → E.pi2 k P.T = 0) := by sorry

end GroupBuyEq.Signup
