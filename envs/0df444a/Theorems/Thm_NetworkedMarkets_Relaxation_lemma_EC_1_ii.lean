-- Prove2me | Theorems.Thm_NetworkedMarkets_Relaxation_lemma_EC_1_ii
-- name    : NetworkedMarkets.Relaxation.lemma_EC_1_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:25:06.480998+00:00
-- url     : https://prove2.me/theorems/c9d96835-0b3f-477b-b38a-4c6d8b8f1665
-- title:
--   Lemma EC.1(ii), p. ec4 (PDF 48) — under Assumptions 1–2 the objective pieces of (7) are C¹, strictly concave/convex, with the boundary slopes (EC.1.1-3), (EC.1.1-7)–(EC.1.1-8)
-- statement:
--   Under the standing assumptions and Assumptions 1–2, let $g_j(q)=F^{-1}_{b_j}(1-q/b_j)\,q$ for $j\in\mathcal B$ and $h_i(q)=F^{-1}_{s_i}(q/s_i)\,q$ for $i\in\mathcal S$ be the pieces of the objective of (7), so that (7) is the framework problem (EC.1) with these $g_j,h_i$ and $w_{ij}=c_i$. Write $g'_j(0)=\lim_{q\downarrow0}g'_j(q)$, $g'_j(b_j)=\lim_{q\uparrow b_j}g'_j(q)$, and likewise for $h_i$ (footnote 22). Then:
--
--   1. **(EC.1.1-1)** each $g_j$ is continuously differentiable and strictly concave on $(0,b_j)$, and continuous at $0$ and at $b_j$ (relative to $[0,b_j]$);
--   2. **(EC.1.1-2)** each $h_i$ is continuously differentiable and strictly convex on $(0,s_i)$, continuous at $0$, and continuous at $s_i$ whenever $h_i(s_i)<\infty$, i.e. whenever $\bar v_{s_i}<\infty$;
--   3. **(EC.1.1-3), (EC.1.1-8)** the limits $g'_j(0)$ and $g'_j(b_j)$ exist in $[-\infty,\infty]$, with
--   $$g'_j(0)>0,\qquad g'_j(b_j)\le 0;$$
--   4. **(EC.1.1-3), (EC.1.1-7)** the limits $h'_i(0)$ and $h'_i(s_i)$ exist in $[-\infty,\infty]$, with
--   $$h'_i(0)=0,\qquad h'_i(s_i)>-\infty.$$
--
--   These are the regularity properties under which Proposition EC.1 applies to (7): existence and uniqueness of the optimal supply-demand vector, finite slopes and the special dual multipliers (EC.3).
--
--   **Formalization Note.** The one-sided limits of the derivative are taken in the extended reals `EReal`; $g'_j(0)>0$ (which includes $>-\infty$) allows the value $+\infty$, as happens when $\bar v_{b_j}=\infty$. The opening clause of Lemma EC.1(ii) ("can be formulated as an instance of the framework problem") is definitional and is not posed.
-- source:
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), p. ec4 (PDF 48), Lemma EC.1(ii); assumptions (EC.1.1-1)–(EC.1.1-3), (EC.1.1-7)–(EC.1.1-8) and footnote 22, p. ec2 (PDF 46)

import Mathlib
import Definitions.Def_NetworkedMarkets_Relaxation_Setting

open Filter Topology

namespace NetworkedMarkets.Relaxation

theorem lemma_EC_1_ii {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (M : Market S B) (hM : M.Standing) :
    -- (EC.1.1-1)
    (∀ j, ContDiffOn ℝ 1 (M.gB j) (Set.Ioo 0 (M.b j)) ∧
      StrictConcaveOn ℝ (Set.Ioo 0 (M.b j)) (M.gB j) ∧
      ContinuousWithinAt (M.gB j) (Set.Icc 0 (M.b j)) 0 ∧
      ContinuousWithinAt (M.gB j) (Set.Icc 0 (M.b j)) (M.b j)) ∧
    -- (EC.1.1-2)
    (∀ i, ContDiffOn ℝ 1 (M.hS i) (Set.Ioo 0 (M.s i)) ∧
      StrictConvexOn ℝ (Set.Ioo 0 (M.s i)) (M.hS i) ∧
      ContinuousWithinAt (M.hS i) (Set.Icc 0 (M.s i)) 0 ∧
      ((M.Fs i).vbar ≠ ⊤ → ContinuousWithinAt (M.hS i) (Set.Icc 0 (M.s i)) (M.s i))) ∧
    -- (EC.1.1-3) and (EC.1.1-8) for buyers: g'_j(0) ∈ (0, ∞], g'_j(b_j) ≤ 0
    (∀ j, ∃ L0 Lb : EReal,
      Tendsto (fun q => ((deriv (M.gB j) q : ℝ) : EReal)) (𝓝[Set.Ioo 0 (M.b j)] 0) (𝓝 L0) ∧
      Tendsto (fun q => ((deriv (M.gB j) q : ℝ) : EReal)) (𝓝[Set.Ioo 0 (M.b j)] (M.b j)) (𝓝 Lb) ∧
      0 < L0 ∧ Lb ≤ 0) ∧
    -- (EC.1.1-3) and (EC.1.1-7) for sellers: h'_i(0) = 0, h'_i(s_i) > -∞
    (∀ i, ∃ Ls : EReal,
      Tendsto (fun q => ((deriv (M.hS i) q : ℝ) : EReal)) (𝓝[Set.Ioo 0 (M.s i)] 0) (𝓝 0) ∧
      Tendsto (fun q => ((deriv (M.hS i) q : ℝ) : EReal)) (𝓝[Set.Ioo 0 (M.s i)] (M.s i)) (𝓝 Ls) ∧
      ⊥ < Ls) := by sorry

end NetworkedMarkets.Relaxation
