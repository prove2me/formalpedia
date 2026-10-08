-- Prove2me | Theorems.Thm_LostSalesOldNew_StateReduction_claim_1
-- name    : LostSalesOldNew.StateReduction.claim_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T18:00:47.05274+00:00
-- url     : https://prove2.me/theorems/2ca9d816-48f7-45a8-8156-d3c65fe27dbd
-- title:
--   Claim 1 — under any policy in Z(s), almost surely the state lies in X(s) from some period on, so all states outside X(s) are transient
-- statement:
--   Consider the lost-sales system with lead time $L\ge 1$ and i.i.d. demands $d_0,d_1,\dots$ with common law $D$ on $[0,\infty)$, where demand is not almost surely zero: $P(d>0)>0$. Let $s=(s_0,\dots,s_L)$ satisfy $s_0\ge s_1\ge\dots\ge s_L\ge 0$, let $z\in Z(s)$ be a stationary policy, and let $x\ge 0$ be any initial state. Let $x_t$ be the state in period $t$ under $z$, started at $x_0=x$. Then, almost surely,
--   $$
--   \exists\, T\ \ \forall\, t\ge T:\qquad x_t\in X(s).
--   $$
--
--   The paper states: "For any policy in $Z(s)$, all states outside $X(s)$ are transient." We state: almost surely the state lies in $X(s)$ from some period on, so every state outside $X(s)$ (indeed the whole complement of $X(s)$) is visited only finitely often. This is the reading the paper's proof establishes — the process started outside $X(s)$ eventually reaches $X(s)$, and once it enters $X(s)$ it never leaves.
--
--   Consequently, to solve the dynamic program one may restrict attention to the compact state space $X(\bar s)$ and the policies $Z(\bar s)$.
--
--   **Formalization Note.** The demand sequence is the coordinate process under the product measure $D^{\otimes\mathbb N}$ (`Measure.infinitePi`), which encodes the paper's independent, stationary, nonnegative demands. The hypothesis $D((0,\infty))>0$ is added: the paper assumes only nonnegative demands, but with $d\equiv 0$ a state with $x_0>s_0$ is never left and the claim fails. Policies are deterministic stationary functions of the state; the initial state is any $x\ge 0$, inside or outside $X(s)$.
-- source:
--   Zipkin, Old and New Methods for Lost-Sales Inventory Systems, Operations Research 56(5) (2008), Claim 1, p. 1259

import Mathlib
import Definitions.Def_LostSalesOldNew_StateReduction_Model

namespace LostSalesOldNew.StateReduction

open MeasureTheory

theorem claim_1 {L : ℕ} (hL : 0 < L) (s : Fin (L + 1) → ℝ) (hs : IsLevelVector s)
    (z : (Fin L → ℝ) → ℝ) (hz : z ∈ Zs s)
    (D : Measure ℝ) (hD : IsDemand D) (hDpos : 0 < D (Set.Ioi 0))
    (x : Fin L → ℝ) (hx : ∀ i, 0 ≤ x i) :
    haveI := hD.isProb
    ∀ᵐ ds ∂(Measure.infinitePi (fun _ : ℕ => D)),
      ∃ T : ℕ, ∀ t, T ≤ t → traj z x ds t ∈ Xs s := by sorry

end LostSalesOldNew.StateReduction
