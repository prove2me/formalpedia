-- Prove2me | Theorems.Thm_NegNetQueue_Meets_Supplement_theorem_4
-- name    : NegNetQueue.Meets.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T11:07:32.723784+00:00
-- url     : https://prove2.me/theorems/9cf83639-e6f8-4b7c-bc8d-4618842b2317
-- title:
--   Theorem 4 — person-hour mean and transform (corrected: completion and recursion indices)
-- statement:
--   Consider the FCFS M/M/c/n queue with arrival rate $\lambda>0$, service rate $\mu>0$ per server, $c\ge1$ servers and waiting-room capacity $n\ge1$. Fix any tagged-customer state $(j,k)$ with $1\le j\le k\le n$. Let $T_{j,k}$ be the total person-hours of exposure to other waiting customers until service starts. It is defined from the published event dynamics and independent exponential event intervals, rather than by the formulas asserted here. Let $Q,N,D_G(\eta)$ be the transient transition matrix, local mean vector, and diagonal local-transform matrix defined in §5. Write $G_{j,k}(\eta)=E[\eta^{T_{j,k}}]$ and $G(\eta)$ for its vector over all states, and $\mathbf1$ for the all-ones vector.
--
--   The matrix $I-Q$ is invertible and the mean vector is finite and given by (8):
--   $$E[T_{j,k}]=\big((I-Q)^{-1}N\big)_{j,k}.$$
--   For every $0<\eta\le1$, all transform integrands are integrable, $I-D_G(\eta)Q$ is invertible, and both forms of (12) hold:
--   $$G(\eta)=(I-D_G(\eta)Q)^{-1}D_G(\eta)(I-Q)\mathbf1
--   =D_G(\eta)\big[QG(\eta)+(I-Q)\mathbf1\big].$$
--   Here $g_k(\eta)=1/(1+N_{j,k}\log(1/\eta))$ is the diagonal entry of $D_G$. The four rows of (13), with $a=\lambda/(\lambda+c\mu)$ and $q=c\mu/(\lambda+c\mu)$, are
--   $$\begin{aligned}
--   G_{1,n}&=g_n,\\
--   G_{1,k}&=g_k(aG_{1,k+1}+q) &&(1\le k<n),\\
--   G_{j,n}&=g_nG_{j-1,n-1} &&(2\le j\le n),\\
--   G_{j,k}&=g_k(aG_{j,k+1}+qG_{j-1,k-1}) &&(2\le j\le k<n).
--   \end{aligned}$$
--   Every function in these rows is evaluated at the same $\eta$. The theorem supplies the mean and survival transform of time-weighted exposure, complementing the distinct-customer law in the published goal Theorem 3. It is a companion result and is not used to prove that goal.
--
--   **Formalization Note** The statement uses a lintegral for the nonnegative mean and asserts that it equals the nonnegative embedding of the displayed finite real matrix value. Neither integrability of exposure nor a recurrence is assumed. Matrix invertibility is an explicit conclusion. No stability restriction $\rho<1$ is needed for a finite waiting room. Capacity one is included.
--
--   Differences from the source:
--   - encoding: The continuous-time FCFS M/M/c/n queue and exponential sojourns on pp. 11–13. → The published event sequence plus i.i.d. Exp(lambda+c mu) holding clocks independent of the whole mark sequence; exposure is an extended nonnegative path sum, including lost arrivals.; reason: Uniformization preserves the queue trajectory and all elapsed exposure. Finiteness is not assumed; the mean is a nonnegative lintegral, and transform integrability is concluded.
--   - correction: The p. 11 prose sends (j,k) to (j-1,k); (13) prints G_{1,k}, G_{t,j,k} in the full row, and omits the last transform argument. → Completion sends (j,k) to (j-1,k-1); the local factors are G_{t,1,k}, G_{t,j,n}, and the final transform is evaluated at eta.; reason: The published dynamics and (9), (11) determine the corrected indices and arguments; no states are excluded.
--   - generalization: The survival parameter in the surrounding application is 0 < eta < 1 (p. 14). → The transform formulas include 0 < eta <= 1.; reason: At eta=1 the actual transform is one, DG is the identity, and the matrix/recursion identities reduce to normalization; the full original domain is retained.
-- source:
--   Hassin, Meilijson & Perlman, Queueing with Negative Network Effects, SSRN 4097977 (version of July 2, 2022), pp. 11–14, Theorem 4; (8), (10), (12), (13)

import Mathlib
import Definitions.Def_NegNetQueue_Meets_Supplement_Exposure

set_option autoImplicit false
open scoped ENNReal Matrix

namespace NegNetQueue.Meets.Supplement

open MeasureTheory

/-- Theorem 4, all of (8), (12) and the four rows of (13).
No moment, absorption, recurrence or invertibility assertion is assumed. -/
theorem theorem_4 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (lam mu : ℝ) (c n : ℕ)
    (hlam : 0 < lam) (hmu : 0 < mu) (hc : 1 ≤ c) (hn : 1 ≤ n)
    (ε : ℕ → Ω → Bool) (τ : ℕ → Ω → ℝ)
    (hseq : IsHoldingSeq P lam mu c ε τ) :
    IsUnit (Matrix.det (1 - Q n lam mu c)) ∧
    (∀ s : State n,
      0 ≤ ((1 - Q n lam mu c)⁻¹ *ᵥ N n lam mu c) s ∧
      (∫⁻ ω, exposure n s.1.1.val s.1.2.val ε τ ω ∂P) =
        ENNReal.ofReal (((1 - Q n lam mu c)⁻¹ *ᵥ N n lam mu c) s)) ∧
    (∀ (η : ℝ), 0 < η → η ≤ 1 →
      (∀ s : State n,
        Integrable (fun ω => survivalPower η
          (exposure n s.1.1.val s.1.2.val ε τ ω)) P) ∧
      IsUnit (Matrix.det (1 - DG n lam mu c η * Q n lam mu c)) ∧
      GFvec P n ε τ η =
        (1 - DG n lam mu c η * Q n lam mu c)⁻¹ *ᵥ
          (DG n lam mu c η *ᵥ ((1 - Q n lam mu c) *ᵥ (fun _ => 1))) ∧
      GFvec P n ε τ η =
        DG n lam mu c η *ᵥ
          (Q n lam mu c *ᵥ GFvec P n ε τ η +
            (1 - Q n lam mu c) *ᵥ (fun _ => 1)) ∧
      totalGF P n 1 n ε τ η = localGF n lam mu c η n ∧
      (∀ k : ℕ, 1 ≤ k → k < n →
        totalGF P n 1 k ε τ η = localGF n lam mu c η k *
          (lam / (lam + c * mu) * totalGF P n 1 (k + 1) ε τ η +
            qComp lam mu c)) ∧
      (∀ j : ℕ, 2 ≤ j → j ≤ n →
        totalGF P n j n ε τ η = localGF n lam mu c η n *
          totalGF P n (j - 1) (n - 1) ε τ η) ∧
      (∀ j k : ℕ, 2 ≤ j → j ≤ k → k < n →
        totalGF P n j k ε τ η = localGF n lam mu c η k *
          (lam / (lam + c * mu) * totalGF P n j (k + 1) ε τ η +
            qComp lam mu c * totalGF P n (j - 1) (k - 1) ε τ η))) := by sorry

end NegNetQueue.Meets.Supplement
