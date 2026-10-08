-- Prove2me | Theorems.Thm_LostSalesOldNew_StateReduction_reaches_Xs
-- name    : LostSalesOldNew.StateReduction.reaches_Xs
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T18:01:23.064523+00:00
-- url     : https://prove2.me/theorems/17f9b203-a4a2-487e-b58d-e3fdafad0694
-- title:
--   Proof of Claim 1 — started outside X(s), the process reaches X(s) along any demand path with divergent cumulative demand
-- statement:
--   Let $L\ge 1$. Let $s=(s_0,\dots,s_L)$ satisfy $s_0\ge s_1\ge\dots\ge s_L\ge 0$, let $z\in Z(s)$, and let $x\ge 0$ be an initial state. Let $(d_t)_{t\ge 0}$ be a demand path with $d_t\ge 0$ for all $t$ and
--   $$
--   \sum_{t=0}^{n-1} d_t \longrightarrow \infty \qquad (n\to\infty).
--   $$
--   Then the state process $x_0=x$, $x_{t+1}=(x_t)_+$ (order $z(x_t)$, demand $d_t$) visits $X(s)$: there is a period $t$ with $x_t\in X(s)$.
--
--   This is the entrance half of the proof of Claim 1: "If the process starts outside $X(s)$, it must eventually reach $X(s)$ because $z(x)=0$ until then."
--
--   **Formalization Note.** The paper leaves implicit why the process must reach $X(s)$; the divergence of the cumulative demand is the pathwise condition under which the sentence holds (with demand identically $0$ and no orders, a state with $x_0>s_0$ stays put forever). It is a hypothesis of this pathwise milestone only; the goal theorem assumes instead an i.i.d. demand law with $P(d>0)>0$, under which the cumulative demand diverges almost surely. The conclusion holds also when $x\in X(s)$ already (take $t=0$).
-- source:
--   Zipkin, Old and New Methods for Lost-Sales Inventory Systems, Operations Research 56(5) (2008), proof of Claim 1, p. 1259

import Mathlib
import Definitions.Def_LostSalesOldNew_StateReduction_Model

namespace LostSalesOldNew.StateReduction

theorem reaches_Xs {L : ℕ} (hL : 0 < L)
    (s : Fin (L + 1) → ℝ) (hs : IsLevelVector s)
    (z : (Fin L → ℝ) → ℝ) (hz : z ∈ Zs s) (x : Fin L → ℝ) (hx : ∀ i, 0 ≤ x i)
    (ds : ℕ → ℝ) (hds : ∀ t, 0 ≤ ds t)
    (hdiv : Filter.Tendsto (fun n => ∑ t ∈ Finset.range n, ds t) Filter.atTop Filter.atTop) :
    ∃ t, traj z x ds t ∈ Xs s := by sorry

end LostSalesOldNew.StateReduction
