-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_pscp_condition_49
-- name    : ManyServerQED.Scheduling.pscp_condition_49
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-07T05:00:32.953644+00:00
-- url     : https://prove2.me/theorems/d547d0c1-df37-431a-a6a3-0e4dbc615eb8
-- title:
--   Proof of Theorem 2(i), pp. 39–40 — the P-SCP satisfies condition (49)
-- statement:
--   Consider the sequence of $k$-class, $n$-server queues with abandonment under Assumptions 1(i), 2 (cost $\tilde L$, Hölder exponent $\varrho$, growth exponent $m_L$) and 3 (moment exponent $m_U$), with discount rate $\gamma>0$. Let $f$ be a $C^2_{\mathrm{pol}}$ classical solution of the HJB equation (41), and let $h:\mathbb R^k\to\mathbb S^k$ be measurable with
--   $$
--   b(x,h(x))\cdot Df(x)+L(x,h(x))=H(x,Df(x)),\qquad x\in\mathbb R^k .
--   $$
--   Let $X^{0,n}\in\mathbb Z^k_+$ with $\hat X^{0,n}=n^{-1/2}(X^{0,n}-\rho n)\to x$, and for each $n\ge 1$ let $X^{n}=X^{n,*}$ solve the system equations (7) from $X^{0,n}$ under the proposed P-SCP $\Psi^{n}=X^{n}-\Phi^{n}$, where $\Phi^n(t)=\Theta[(\mathbb 1\cdot X^n(t)-n)^+h(\hat X^n(t))]$ when (31) holds and $\Phi^n$ is given by the static priority rule otherwise (pp. 18–19). Fix $u_0\in\mathbb S^k$ and let $u^n$ be given by (47):
--   $$
--   u^n_t=\frac{\Phi^n(t)}{(\mathbb 1\cdot X^n(t)-n)^+}\ \text{ if } \mathbb 1\cdot X^n(t)-n>0,\qquad u^n_t=u_0\ \text{ otherwise.}
--   $$
--   With
--   $$
--   K^n_t=b(\hat X^n_t,u^n_t)\cdot Df(\hat X^n_t)+L(\hat X^n_t,u^n_t)-H(\hat X^n_t,Df(\hat X^n_t))\qquad(48),
--   $$
--   where $L(x,u)=\tilde L((\mathbb 1\cdot x)^+u,\;x-(\mathbb 1\cdot x)^+u)$, the P-SCP satisfies condition (49):
--   $$
--   \int_0^{\cdot} e^{-\gamma s}K^n_s\,ds\;\Rightarrow\;0 .
--   $$
--   Since the limit is the zero path, convergence in distribution is stated equivalently as uniform convergence on compact time intervals in probability: for every $T\ge 0$ and $\varepsilon>0$, $P\big(\sup_{t\le T}|\int_0^t e^{-\gamma s}K^n_s\,ds|\ge\varepsilon\big)\to 0$.
--
--   This is the key step of the proof of Theorem 2(i) (pp. 39–40): it verifies that the P-SCP meets the hypothesis (49) of Theorem 4(ii), which together with Theorem 4(i) yields the asymptotic optimality of the P-SCP.
--
--   **Formalization notes.** The hypotheses are exactly those of the goal theorem `pscp_asymptotically_optimal` (Theorem 2(i)), plus the arbitrary $u_0\in\mathbb S^k$ of (47). The solution $X^{n,*}$ is hypothesized to solve (7) under the P-SCP feedback; Proposition 1 makes it unique and admissible.
-- source:
--   Atar, Mandelbaum & Reiman, Scheduling a Multi Class Queue with Many Exponential Servers: Asymptotic Optimality in Heavy Traffic, arXiv:math/0407058v1 (reprint of Ann. Appl. Probab. 14(3), 2004), pp. 39–40, proof of Theorem 2, part (i) 'The P-SCP' (conditions (47)–(49) p. 30–31, (72)–(75) pp. 39–40)

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_ManyServerQED_Scheduling_Diffusion
import Definitions.Def_ManyServerQED_Scheduling_Model
import Definitions.Def_ManyServerQED_Scheduling_Policy

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ManyServerQED.Scheduling

open BellWilliams2001.ThresholdPolicy

/-- Proof of Theorem 2(i) (pp. 39–40), "(i) The P-SCP": under Assumptions 1(i), 2 and 3, with `f`
a `C²_pol` solution of the HJB equation (41) and `h : ℝ^k → 𝕊^k` a measurable selection of its
minimizers, the processes `X^{n,∗}` controlled by the proposed P-SCP
`Ψ^{n,∗} = X^{n,∗} − Φ̃ₙ(X^{n,∗})` (pp. 18–19), started from `X^{0,n}` with `X̂^{0,n} → x`, satisfy
condition (49): `∫₀^· e^{−γs} Kⁿ_s ds ⇒ 0`, where
`Kⁿ_s = b(X̂ⁿ_s, uⁿ_s) · Df(X̂ⁿ_s) + L(X̂ⁿ_s, uⁿ_s) − H(X̂ⁿ_s, Df(X̂ⁿ_s))` (48) and `uⁿ` is given by
(47) with a fixed `u₀ ∈ 𝕊^k`. Convergence to the zero path is stated as u.o.c. convergence in
probability. -/
theorem pscp_condition_49 {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} [NeZero k]
    (M : SystemSequence Ω k)
    (Lt : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (ϱ mL mU γ : ℝ)
    (hA2 : Assumption2 Lt ϱ mL) (hA3 : M.Assumption3 mL mU) (hγ : 0 < γ)
    (f : (Fin k → ℝ) → ℝ) (hf : IsC2Pol f)
    (hHJB : IsHJBSolution M.diffData (costOfTilde Lt) γ f)
    (h : (Fin k → ℝ) → (Fin k → ℝ)) (hh_meas : Measurable h)
    (hh_mem : ∀ y, h y ∈ stdSimplex ℝ (Fin k))
    (hh_min : ∀ y, ∑ i, drift M.diffData y (h y) i * grad f y i + costOfTilde Lt y (h y) =
      hamiltonian M.diffData (costOfTilde Lt) y (grad f y))
    (u0 : Fin k → ℝ) (hu0 : u0 ∈ stdSimplex ℝ (Fin k))
    (X0 : ℕ → Fin k → ℕ) (x : Fin k → ℝ)
    (hX0 : Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x))
    (Xs : ℕ → Ω → ℝ → Fin k → ℕ)
    (hXs : ∀ n, 1 ≤ n → M.IsControlled n (X0 n) (fun ω t i => (Xs n ω t i : ℝ))
      (fun ω t i => (Xs n ω t i : ℝ) - M.pscpPhi h n (Xs n ω t) i)) :
    UocInProb M.P
      (fun n ω t => ![∫ s in (0 : ℝ)..t, Real.exp (-γ * s) *
        (∑ i, drift M.diffData (M.Xhat n (fun ω t i => (Xs n ω t i : ℝ)) ω s)
              (uProc n u0 (fun ω t i => (Xs n ω t i : ℝ))
                (fun ω t i => (Xs n ω t i : ℝ) - M.pscpPhi h n (Xs n ω t) i) ω s) i *
            grad f (M.Xhat n (fun ω t i => (Xs n ω t i : ℝ)) ω s) i +
          costOfTilde Lt (M.Xhat n (fun ω t i => (Xs n ω t i : ℝ)) ω s)
            (uProc n u0 (fun ω t i => (Xs n ω t i : ℝ))
              (fun ω t i => (Xs n ω t i : ℝ) - M.pscpPhi h n (Xs n ω t) i) ω s) -
          hamiltonian M.diffData (costOfTilde Lt) (M.Xhat n (fun ω t i => (Xs n ω t i : ℝ)) ω s)
            (grad f (M.Xhat n (fun ω t i => (Xs n ω t i : ℝ)) ω s)))])
      (fun _ => 0) := by sorry

end ManyServerQED.Scheduling
