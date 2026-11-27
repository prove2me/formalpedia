-- Prove2me | Theorems.Thm_MulticlassQNet_SingleStation_Supplement_theorem_7_1_third_order_space
-- name    : MulticlassQNet.SingleStation.Supplement.theorem_7_1_third_order_space
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T05:32:27.122899+00:00
-- url     : https://prove2.me/theorems/a7450ffd-ea13-4fbc-8250-d94709ed05e8
-- title:
--   Theorem 7.1 — third-order interactions: the achievable (n, I, H, M, J) satisfies (48)–(53) (corrected: every coefficient of the cubic drift, (49) for all r ≠ r′)
-- statement:
--   Consider an open multiclass network with fixed routing (§2), traffic solution $\lambda$ of $\lambda_r=\lambda_{0r}+\sum_{r'}\lambda_{r'}p_{r'r}$, the network open (that solution is unique), and exit probabilities $p_{r0}=1-\sum_sp_{rs}$. For a Markovian sequencing policy satisfying the modified Assumption A (unique invariant distribution, $E[n_r^3]<\infty$ for every $r$), let
--
--   $$n_r=E[n_r],\quad I_{rj}=E[1\{B_r\}n_j],\quad H_{rjk}=E[1\{B_r\}n_jn_k],\quad M_{jk}=E[n_jn_k],\quad J_{rjk}=E[n_rn_jn_k].$$
--
--   Then:
--
--   1. For every vector $f=(f_1,\dots,f_R)$ of f-parameters,
--   $$\begin{aligned}
--   0={}&\sum_r\lambda_{0r}\Big[3f_r\sum_{j,k}f_jf_kM_{jk}+3f_r^2\sum_jf_jn_j+f_r^3\Big]
--   +3\sum_r\mu_r\Big\{\sum_sp_{rs}(f_s-f_r)-p_{r0}f_r\Big\}\sum_{j,k}f_jf_kH_{rjk}\\
--   &+3\sum_r\mu_r\Big\{\sum_sp_{rs}(f_s-f_r)^2+p_{r0}f_r^2\Big\}\sum_jf_jI_{rj}
--   +\sum_r\lambda_r\Big\{\sum_sp_{rs}(f_s-f_r)^3-p_{r0}f_r^3\Big\}.
--   \end{aligned}$$
--   Equating its coefficients to zero gives (48) for the monomials $f_r^3$, (49) for the $R(R-1)$ monomials $f_r^2f_{r'}$, and (50) for the monomials $f_rf_jf_k$, $r<j<k$. For instance the $f_r^3$ coefficient is
--   $$-\lambda_r+\sum_{r'}\lambda_{r'}p_{r'r}+3\mu_r(1-p_{rr})I_{rr}+3\sum_{r'\ne r}\mu_{r'}p_{r'r}I_{r'r}-3\mu_rH_{rrr}+3\sum_{r'}\mu_{r'}p_{r'r}H_{r'rr}+\lambda_{0r}+3\lambda_{0r}n_r+3\lambda_{0r}M_{rr}=0.\quad(48)$$
--   2. $\sum_{l\in C_i}I_{lr}\le n_r$ for all $r,i$ (51), and $\sum_{l\in C_i}H_{ljk}\le M_{jk}$ for all $j,k,i$ (52).
--   3. $n_r,I_{rj},H_{rjk},M_{jk},J_{rjk}\ge0$ (53).
--
--   Adding the variables $H$, $M$, $J$ captures interactions among three classes and puts the second moments $M_{jj}=E[n_j^2]$ into the space, so that bounds on objectives involving variances become available.
--
--   **Formalization Note** The polynomial is `cubicPoly` of the `ThirdMoments` definition, evaluated at the actual moments; policies, $I$ and $n$ are the published ones. The traffic and openness hypotheses are the standing setup of §§2 and 4.1 under which (48)–(49) are written with $\lambda_r$ (by the first-order drift, $\mu_rE[1\{B_r\}]=\lambda_r$). The §4.1 load condition $\sum_{r\in C_i}\lambda_r/\mu_r<1$ is not assumed: the identity does not use it, and it follows from the modified Assumption A in an open network.
--
--   Differences from the source:
--   - correction: the printed coefficient equations (48)–(50) → Lean states the vanishing of the whole cubic polynomial for every $f$, which is equivalent to all its coefficient equations; reason: the proof (p. 29) equates every coefficient to zero, while the printed (48) sums $\lambda_{r'}p_{r'r}$ over an index written $r=1,\dots,R$, (49) lacks "$=0$" and lists only $r>r'$ although all $R(R-1)$ ordered monomials $f_r^2f_{r'}$ are needed (their coefficients differ), and (50) has $-\mu_jp_{jk}I_{jk}$ where the expansion of the drift of $R^3$ gives $-\mu_jp_{jr}I_{jk}$
--   - generalization: §4.1 (p. 13) assumes $\sum_{r\in C_i}\lambda_r/\mu_r<1$ at every station for the open network → Lean does not assume it; reason: the conclusion's derivation does not use it, and it is implied by the modified Assumption A in an open network (a station busy with probability one under a unique invariant law contradicts openness), so every source instance is covered
-- source:
--   Bertsimas, Paschalidis, Tsitsiklis, Optimization of Multiclass Queueing Networks: Polyhedral and Nonlinear Characterizations of Achievable Performance, MIT Sloan WP #3509-92-MSA (Dec. 1992), pp. 28–29, Theorem 7.1, Eqs. (48)–(53); variables and modified Assumption A p. 28; proof p. 29

import Mathlib
import Definitions.Def_MulticlassQNet_FirstOrder_Network
import Definitions.Def_MulticlassQNet_FirstOrder_Dynamics
import Definitions.Def_MulticlassQNet_SingleStation_Supplement_ThirdMoments

namespace MulticlassQNet.SingleStation.Supplement

open MulticlassQNet.FirstOrder

/-- Theorem 7.1 (p. 28): in an open multiclass network with fixed routing, for every sequencing
policy satisfying the modified Assumption A (unique invariant law, `E[n_r³] < ∞`), the variables
`n_r`, `I_{rj}`, `H_{rjk}`, `M_{jk}`, `J_{rjk}` satisfy: the cubic polynomial `cubicPoly` vanishes
for every f-parameter vector `f` (equivalently, all its coefficients vanish: (48), (49) and (50)
with the printing errors repaired), the bounds (51) and (52), and nonnegativity (53). -/
theorem theorem_7_1_third_order_space {N R : ℕ} (net : Network N R) (lam : Fin R → ℝ)
    (htraffic : net.IsTrafficSolution lam) (hopen : net.IsOpen)
    (P : Policy net) (π : (Fin R → ℕ) → ℝ) (hA : ThirdOrder.AssumptionA3 P π) :
    -- (48)–(50): every coefficient of the cubic in f vanishes
    (∀ f : Fin R → ℝ, cubicPoly net lam f (meanNum π) (P.busyMoment π) (ThirdOrder.H P π)
        (secondMoment π) = 0) ∧
    -- (51)
    (∀ i r, ∑ l ∈ net.C i, P.busyMoment π l r ≤ meanNum π r) ∧
    -- (52)
    (∀ i j k, ∑ l ∈ net.C i, ThirdOrder.H P π l j k ≤ secondMoment π j k) ∧
    -- (53)
    (∀ r, 0 ≤ meanNum π r) ∧ (∀ r j, 0 ≤ P.busyMoment π r j) ∧
    (∀ r j k, 0 ≤ ThirdOrder.H P π r j k) ∧ (∀ j k, 0 ≤ secondMoment π j k) ∧
    (∀ r j k, 0 ≤ thirdMoment π r j k) := by sorry

end MulticlassQNet.SingleStation.Supplement
