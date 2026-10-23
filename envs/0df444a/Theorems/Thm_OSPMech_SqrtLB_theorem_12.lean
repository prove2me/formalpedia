-- Prove2me | Theorems.Thm_OSPMech_SqrtLB_theorem_12
-- name    : OSPMech.SqrtLB.theorem_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:06:06.046539+00:00
-- url     : https://prove2.me/theorems/4a074f35-cb07-4c11-b0c7-755856377ea1
-- title:
--   Theorem 12, p. 12 — no OSP mechanism for scheduling m = n = c² identical jobs on related machines with domains {L, M, H} is better than √n-approximate
-- statement:
--   Fix an integer $c \ge 2$ and let $n = m = c^2$, so $\sqrt n = c$. Consider scheduling $m$ identical jobs on $n$ related machines, where agent $i$ controls machine $i$ and has a processing time per job in the three-value domain $D_i = \{L, M, H\}$, with
--   $$0 < L, \qquad M \ge m \cdot L, \qquad H \ge m\sqrt n \cdot M.$$
--   Let $(\mathcal T, \mathbf p)$ be any extensive-form mechanism, with implementation tree $\mathcal T$ and payment function $\mathbf p$, that is obviously strategyproof on $D = \{L, M, H\}^n$ for the costs $t_i \cdot f_i$ and whose outcome on every profile of $D$ assigns all $m$ jobs. Then there is a profile $\mathbf b \in D$ on which
--   $$\max_{i} b_i f_i(\mathbf b) \;\ge\; \sqrt n \cdot \mathrm{OPT}(\mathbf b),$$
--   where $\mathrm{OPT}(\mathbf b)$ is the least makespan of a schedule of the $m$ jobs. Equivalently, no such mechanism is $k$-approximate for any $k < \sqrt n$.
--
--   Obvious strategyproofness asks that truth-telling remain dominant for agents who reason only about what they have observed in the execution so far. The theorem shows that this costs a factor $\sqrt n$ in makespan already for three-value domains, whereas with two-value domains an optimal OSP mechanism exists (Proposition 11), and a matching $O(\sqrt n)$ upper bound holds.
--
--   **Formalization Note.** The statement is posed in the instance family of the paper's proof (p. 12): $n = m = c^2$ with $c \ge 2$ (the paper's $c > 1$), $M \ge mL$ and $H \ge m\sqrt n M$; non-square $n$ is not claimed. $0 < L$ reads the paper's non-negative costs with $L < M < H$, and makes $\mathrm{OPT} > 0$, so the conclusion is equivalent to "not $k$-approximate for any $k < \sqrt n$". Payments are a function of the declared profile, which allows more mechanisms and so strengthens the impossibility.
-- source:
--   Ferraioli, Meier, Penna, Ventre, On the approximation guarantee of obviously strategyproof mechanisms, arXiv:1805.04190v2, p. 12, Theorem 12 (instance family p. 12; proof p. 13)

import Mathlib
import Definitions.Def_OSPMech_SqrtLB_Model

namespace OSPMech.SqrtLB
theorem theorem_12 (c : ℕ) (hc : 2 ≤ c) (L Mid H : ℝ) (hL : 0 < L)
    (hM : ((c ^ 2 : ℕ) : ℝ) * L ≤ Mid) (hH : ((c ^ 2 : ℕ) : ℝ) * c * Mid ≤ H)
    (t : ImplTree (c ^ 2) (Fin (c ^ 2) → ℕ)) (p : (Fin (c ^ 2) → ℝ) → Fin (c ^ 2) → ℝ)
    (hsched : IsSchedule (c ^ 2) (fun _ => {L, Mid, H}) t)
    (hosp : IsOSP (fun _ => {L, Mid, H}) schedCost t p) :
    ∃ b : Fin (c ^ 2) → ℝ, InDomain (fun _ => {L, Mid, H}) b ∧
      (c : ℝ) * optMakespan (c ^ 2) b ≤ makespan b (outcome t b) := by sorry
end OSPMech.SqrtLB
