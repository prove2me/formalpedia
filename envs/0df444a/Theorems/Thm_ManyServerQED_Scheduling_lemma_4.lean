-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_lemma_4
-- name    : ManyServerQED.Scheduling.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:47:07.661249+00:00
-- url     : https://prove2.me/theorems/ec581f19-5012-436c-be88-053d780bd7e6
-- title:
--   Lemma 4(i)–(ii) — FCLT for the primitives and fluid limit $(\bar\Psi^n,\bar\Phi^n)\Rightarrow(\rho,0)$
-- statement:
--   Let Assumptions 1(i) and 3 hold, let $\hat X^{0,n}\to x$, and let $(\Psi^n,X^n)$ be work-conserving admissible SCPs started from $X^{0,n}$. Then:
--   1. $(\hat A^n,\hat S^n,\hat R^n)\Rightarrow(A,S,R)$, where $A$, $S$ and $R$ are independent driftless Brownian motions with covariance matrices $\operatorname{diag}(\lambda_iC^2_{U,i})$, $\operatorname{diag}(\mu_i)$ and $\operatorname{diag}(\theta_i)$;
--   2. the fluid-scaled processes converge to a constant:
--   $$
--   (\bar\Psi^n,\bar\Phi^n)\Rightarrow(\rho,0)\quad\text{in }(\mathbb D(\mathbb R^k))^2.
--   $$
--
--   Part 1 identifies the limiting noise; part 2 is the state-space concentration used throughout Section 4.
--
--   **Formalization Note** In part 1 the limit is written as $\sigma_jB_j$ with $3k$ independent standard Brownian motions $B_j$ and $\sigma=(\sqrt{\lambda_iC^2_{U,i}})_i,(\sqrt{\mu_i})_i,(\sqrt{\theta_i})_i$. A rate $\theta_i=0$ gives the zero process. Weak convergence to a continuous limit is stated in the coupling form of the published `CouplingConverges`: a Skorokhod representation with almost-sure uniform convergence on compacts, which is equivalent to $J_1$ weak convergence for such limits. Part 2 has a deterministic limit; it is stated as convergence uniformly on compacts in probability (`UocInProb`) of each component, which is equivalent to joint weak convergence. Part (iii) of the lemma (tightness of $(\hat X^n,Y^n,Z^n,\hat W^n)$) is not formalized. Only Assumptions 1(i) and 3 of "the assumptions of Theorem 4(i)" are used.
-- source:
--   Atar, Mandelbaum & Reiman, Scheduling a Multi Class Queue with Many Exponential Servers: Asymptotic Optimality in Heavy Traffic, arXiv:math/0407058v1 (reprint of Ann. Appl. Probab. 14(3), 2004), p. 33, Lemma 4(i)-(ii)

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_ManyServerQED_Scheduling_Diffusion
import Definitions.Def_ManyServerQED_Scheduling_Model
import Definitions.Def_ManyServerQED_Scheduling_Policy

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ManyServerQED.Scheduling

open BellWilliams2001.ThresholdPolicy

/-- Lemma 4(i)–(ii) (p. 33), for a sequence of work-conserving admissible SCPs started from
`X^{0,n}` with `X̂^{0,n} → x`, under Assumptions 1(i) and 3:
(i) `(Âⁿ, Ŝⁿ, R̂ⁿ) ⇒ (A, S, R)`, where `A`, `S`, `R` are independent driftless Brownian motions
with covariance matrices `diag(λᵢC²_{U,i})`, `diag(µᵢ)`, `diag(θᵢ)` (written `σⱼ Bⱼ` with `3k`
independent standard Brownian motions `Bⱼ`);
(ii) `(Ψ̄ⁿ, Φ̄ⁿ) ⇒ (ρ, 0)`, i.e. `Ψ̄ⁿ → ρ` and `Φ̄ⁿ → 0` uniformly on compacts in probability. -/
theorem lemma_4 {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (M : SystemSequence Ω k) (mL mU : ℝ)
    (hA3 : M.Assumption3 mL mU) (X0 : ℕ → Fin k → ℕ) (x : Fin k → ℝ)
    (hX0 : Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x))
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ)
    (hpol : ∀ n, 1 ≤ n → M.IsSCP n (X0 n) (X n) (Ψ n) ∧ M.IsAdmissible n (X n) (Ψ n) ∧
      IsWorkConserving n (X n) (Ψ n)) :
    (∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (B : Fin (k + k + k) → ℝ≥0 → Ω' → ℝ),
      IsProbabilityMeasure P' ∧ (∀ j, IsBrownianReal (B j) P') ∧
      iIndepFun (fun j ω (t : ℝ≥0) => B j t ω) P' ∧
      CouplingConverges M.P P'
        (fun n ω t => Fin.append (Fin.append (M.Ahat n ω t) (M.Shat n ω t)) (M.Rhat n ω t))
        (fun ω t j => Fin.append (Fin.append (fun i => Real.sqrt (M.lam i * M.cU2 i))
            (fun i => Real.sqrt (M.mu i))) (fun i => Real.sqrt (M.theta i)) j *
          B j t.toNNReal ω)) ∧
    UocInProb M.P (fun n ω t => Psibar n (Ψ n) ω t) (fun _ => M.rho) ∧
    UocInProb M.P (fun n ω t => Phibar n (X n) (Ψ n) ω t) (fun _ => 0) := by sorry

end ManyServerQED.Scheduling
