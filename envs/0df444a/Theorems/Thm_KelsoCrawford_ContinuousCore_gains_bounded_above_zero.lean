-- Prove2me | Theorems.Thm_KelsoCrawford_ContinuousCore_gains_bounded_above_zero
-- name    : KelsoCrawford.ContinuousCore.gains_bounded_above_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:32:55.504513+00:00
-- url     : https://prove2.me/theorems/d8402fc3-01b4-4042-8544-2aa1f1f9bbf0
-- title:
--   Section 4, equations (8)–(11) — uniform positive coalition gain
-- statement:
--   Let a finite continuous-salary market have strictly increasing continuous utilities, (MP), (NFL), reservation salaries representing the same unemployment utility for each worker, and gross substitutes for every firm at all real salary vectors. If the market has no strict-core allocation, then some $H>0$ works uniformly over all individually rational allocations $A$: a firm $j$ and worker set $C$ can choose salaries $r_i$ that leave each worker in $C$ at least as well off and increase firm $j$’s profit by at least $H$:
--
--   $$\forall A\in\mathrm{IR}(M),\quad\exists j,C,r:\quad u_i(j,r_i)\ge u_i(A(i),s_i)\ (i\in C),\qquad \pi_j(C,r)\ge\pi_j(C_j(A),s)+H.$$
--
--   Here $C_j(A)$ is the set of workers firm $j$ hires at $A$, $s$ is $A$'s salary schedule, and $A(i)$ is worker $i$'s firm.
--
--   In the paper, $\rho_{ij}$ is defined by $u^i(j;\rho_{ij})=u^i[\phi(i);s_{i\phi(i)}]$, $D[(j,C);A]=y^j(C)-\sum_{i\in C}\rho_{ij}-y^j(C^j_\phi)+\sum_{i\in C^j_\phi}s_{ij}$ is the gain of the coalition $(j,C)$ (8), $F(A)=\max_{(j,C)}D$ (9), $G(\phi)$ is the minimum of $F$ over the individually rational salary schedules of the assignment $\phi$ (10), and $H=\min_\phi G(\phi)$ (11); the claim is that $H>0$ when there is no strict core allocation. Since paying worker $i$ any $r_{ij}$ with $u^i(j;r_{ij})\ge u^i[\phi(i);s_{i\phi(i)}]$ costs at least $\rho_{ij}$, the statement above is the claim $F\ge H>0$ on all individually rational allocations. It supplies a unit of measurement independent of the allocation.
--
--   **Formalization Note** The statement quantifies over admissible coalition salaries directly instead of using $\rho_{ij}$, which need not exist when $u^i(j;\cdot)$ is strictly increasing and continuous but bounded.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), p. 1491, Section 4, proof of Theorem 2, equations (8)–(11)

import Mathlib
import Definitions.Def_KelsoCrawford_ContinuousCore_Model

namespace KelsoCrawford.ContinuousCore

theorem gains_bounded_above_zero {W F : Type}
    [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F] [Nonempty F]
    (M : Market W F) (hu : M.UtilityRegular) (hMP : M.MP) (hNFL : M.NFL)
    (hres : M.ReservationSalaries)
    (hGS : ∀ j, KelsoCrawford.Process.GrossSubstitutesOn (M.y j) Set.univ)
    (hnocore : ¬ ∃ A : Allocation W F, M.IsStrictCore anySalary A) :
    ∃ H : ℝ, 0 < H ∧
      ∀ A : Allocation W F, M.IsIR A →
        ∃ (j : F) (C : Finset W) (r : W → ℝ),
          (∀ i ∈ C, M.u i (A.assign i) (A.sal i) ≤ M.u i j (r i)) ∧
          KelsoCrawford.Process.profit (M.y j) (A.hired j) A.sal + H ≤ KelsoCrawford.Process.profit (M.y j) C r := by sorry

end KelsoCrawford.ContinuousCore
