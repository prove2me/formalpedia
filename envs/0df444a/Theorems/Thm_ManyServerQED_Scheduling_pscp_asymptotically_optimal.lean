-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_pscp_asymptotically_optimal
-- name    : ManyServerQED.Scheduling.pscp_asymptotically_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:47:13.605422+00:00
-- url     : https://prove2.me/theorems/73bb8eb9-611d-4221-8d0a-5d28c7ac5626
-- title:
--   Theorem 2(i) — the HJB-based preemptive policy is asymptotically optimal among work-conserving admissible policies
-- statement:
--   Consider the sequence of $k$-class, $n$-server queues with abandonment under Assumptions 1(i), 2 (cost $\tilde L$, Hölder exponent $\varrho$, growth exponent $m_L$) and 3 (moment exponent $m_U$), with discount rate $\gamma>0$. Let $f$ be a $C^2_{\mathrm{pol}}$ classical solution of the HJB equation (41) for the limit data. Let $h:\mathbb R^k\to\mathbb S^k$ be measurable with
--   $$
--   b(x,h(x))\cdot Df(x)+L(x,h(x))=H(x,Df(x)),\qquad x\in\mathbb R^k.
--   $$
--   Let $X^{0,n}\in\mathbb Z^k_+$ with $\hat X^{0,n}=n^{-1/2}(X^{0,n}-\rho n)\to x$. For each $n\ge1$ let $X^{n,*}$ solve the system equations (7) from $X^{0,n}$ under the proposed P-SCP $\Psi^{n,*}(t)=X^{n,*}(t)-\Phi^{n,*}(t)$, where $\Phi^{n,*}(t)$ is given by (29) when (31) holds and by the priority rule otherwise.
--
--   Then the limit
--   $$
--   \lim_{n\to\infty}E\int_0^\infty e^{-\gamma t}\tilde L(\hat\Phi^{n,*}_t,\hat\Psi^{n,*}_t)\,dt
--   $$
--   exists and is finite. Moreover, for every sequence $\Psi^n$ of work-conserving admissible SCPs started from $X^{0,n}$,
--   $$
--   \lim_{n\to\infty}E\int_0^\infty e^{-\gamma t}\tilde L(\hat\Phi^{n,*}_t,\hat\Psi^{n,*}_t)\,dt\le\liminf_{n\to\infty}E\int_0^\infty e^{-\gamma t}\tilde L(\hat\Phi^n_t,\hat\Psi^n_t)\,dt.\qquad(32)
--   $$
--
--   This is the paper's main asymptotic-optimality result for the preemptive policy built from the diffusion control problem.
--
--   **Formalization Note**
--   - $f$ and $h$ are hypotheses. Theorem 3 shows that $f$ exists and is unique, and its proof constructs a measurable minimizer selection $h$. The pointwise minimizer identity is the property of $h$ that the paper's proof of Theorem 2 uses (p. 39). An arbitrary optimal Markov policy could differ from it on the Lebesgue-null lattice where $\hat X^n$ lives.
--   - The solution $X^{n,*}$ is hypothesized; Proposition 1 makes it exist, unique and admissible.
--   - Initial states are integer vectors with $\hat X^{0,n}\to x$. Assumption 1(ii) is not imposed: neither the P-SCP nor the comparators are required to start from a prescribed split $(\Phi^{0,n},\Psi^{0,n})$; each chooses $\Psi^n(0)$.
--   - Costs are in $[0,\infty]$, and "finite" is $c<\infty$. Remark 2's identification of the limit with $V(x)$ is not part of the statement.
-- source:
--   Atar, Mandelbaum & Reiman, Scheduling a Multi Class Queue with Many Exponential Servers: Asymptotic Optimality in Heavy Traffic, arXiv:math/0407058v1 (reprint of Ann. Appl. Probab. 14(3), 2004), p. 20, Theorem 2(i) (P-SCP pp. 18-19; Assumption 3 p. 20)

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_ManyServerQED_Scheduling_Diffusion
import Definitions.Def_ManyServerQED_Scheduling_Model
import Definitions.Def_ManyServerQED_Scheduling_Policy

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ManyServerQED.Scheduling

/-- Theorem 2(i) (p. 20): under Assumptions 1(i), 2 and 3, let `f` be a `C²_pol` classical solution of
the HJB equation (41) and `h : ℝ^k → 𝕊^k` a measurable selection of its minimizers, and let
`X^{0,n} ∈ ℤ^k_+` with `X̂^{0,n} → x`. Let `X^{n,∗}` solve (7) under the proposed P-SCP
`Ψ^{n,∗}(t) = X^{n,∗}(t) − Φ̃ₙ(X^{n,∗}(t))` (pp. 18–19). Then the cost of the P-SCP converges to a
finite limit `c`, and `c ≤ liminf_n Cⁿ` for every sequence of work-conserving admissible SCPs
started from `X^{0,n}`. -/
theorem pscp_asymptotically_optimal {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} [NeZero k]
    (M : SystemSequence Ω k)
    (Lt : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (ϱ mL mU γ : ℝ)
    (hA2 : Assumption2 Lt ϱ mL) (hA3 : M.Assumption3 mL mU) (hγ : 0 < γ)
    (f : (Fin k → ℝ) → ℝ) (hf : IsC2Pol f)
    (hHJB : IsHJBSolution M.diffData (costOfTilde Lt) γ f)
    (h : (Fin k → ℝ) → (Fin k → ℝ)) (hh_meas : Measurable h)
    (hh_mem : ∀ y, h y ∈ stdSimplex ℝ (Fin k))
    (hh_min : ∀ y, ∑ i, drift M.diffData y (h y) i * grad f y i + costOfTilde Lt y (h y) =
      hamiltonian M.diffData (costOfTilde Lt) y (grad f y))
    (X0 : ℕ → Fin k → ℕ) (x : Fin k → ℝ)
    (hX0 : Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x))
    (Xs : ℕ → Ω → ℝ → Fin k → ℕ)
    (hXs : ∀ n, 1 ≤ n → M.IsControlled n (X0 n) (fun ω t i => (Xs n ω t i : ℝ))
      (fun ω t i => (Xs n ω t i : ℝ) - M.pscpPhi h n (Xs n ω t) i)) :
    ∃ c : ℝ≥0∞, c < ⊤ ∧
      Tendsto (fun n => M.queueCost Lt γ n (fun ω t i => (Xs n ω t i : ℝ))
        (fun ω t i => (Xs n ω t i : ℝ) - M.pscpPhi h n (Xs n ω t) i)) atTop (𝓝 c) ∧
      ∀ X Ψ : ℕ → Ω → ℝ → Fin k → ℝ,
        (∀ n, 1 ≤ n → M.IsSCP n (X0 n) (X n) (Ψ n) ∧ M.IsAdmissible n (X n) (Ψ n) ∧
          IsWorkConserving n (X n) (Ψ n)) →
        c ≤ liminf (fun n => M.queueCost Lt γ n (X n) (Ψ n)) atTop := by sorry

end ManyServerQED.Scheduling
