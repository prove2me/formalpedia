-- Prove2me | Theorems.Thm_MultiServerAppt_dphs_exact_evaluation
-- name    : MultiServerAppt.dphs_exact_evaluation
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:05:38.119049+00:00
-- url     : https://prove2.me/theorems/8c49af62-6dbd-44c2-9f69-07e4c1d87c1f
-- title:
--   §4.1-§4.2 — exact evaluation of the D/PH/s appointment system (corrected: $S^{(1)}=S$)
-- statement:
--   Let $s\ge 1$ servers serve $n=s+m>s$ clients at the schedule $x\ge 0$, first-come first-served, with i.i.d. service times $B_c\sim\mathrm{PH}(\alpha,S)$, and let $T,c_I,c_O\in\mathbb R$. Let $(\alpha_{s+i},S_{s+i})$ be the representation built by the recursion of §4.1. Then:
--
--   1. For $0\le i\le m$, the system after client $s+i$ follows $p^{(s+i)}(u)=\alpha_{s+i}\exp(S_{s+i}u)$, in the sense of `SystemLaw`.
--   2. For $1\le i\le m$ and $t\ge 0$: $F_{W_{s+i}}(t)=1-\alpha_i^{\mathrm{wait}}\exp(S_i^{\mathrm{wait}}t)\mathbf 1$.
--   3. For $1\le i\le m$: $S_i^{\mathrm{wait}}$ is nonsingular, $W_{s+i}$ is integrable, and $\mathbb E W_{s+i}=-\alpha_i^{\mathrm{wait}}(S_i^{\mathrm{wait}})^{-1}\mathbf 1$.
--   4. $\sum_{i=s+1}^n\mathbb E W_i=\sum_{i=1}^{n-s}-\alpha_i^{\mathrm{wait}}(S_i^{\mathrm{wait}})^{-1}\mathbf 1$, Eq. (17).
--   5. For $1\le i\le m$ and $t\ge 0$: $F_{M_{s+i}}(t)=1-\alpha_{s+i}\exp(S_{s+i}t)\mathbf 1$; $S_{s+i}$ is nonsingular; $M_{s+i}$ is integrable; and $\mathbb E M_{s+i}=-\alpha_{s+i}S_{s+i}^{-1}\mathbf 1$.
--   6. $I^{(s)}$ is integrable and $\mathbb E I^{(s)}=s(\mathbb E M_n+t_n)-\sum_{i=1}^n\mathbb E B_i$, Eq. (18).
--   7. $O^{(s)}$ is integrable and $\mathbb E O^{(s)}=s\int_0^\infty\max\{t+t_n-T,0\}f(t)\,\mathrm dt$, with $f$ the density of $F_{M_n}$, Eq. (19).
--   8. The objective of Eq. (20) equals the expression `objective` in the matrices:
--
--   $$c_I\mathbb E I^{(s)}+\sum_{i=s+1}^n\mathbb E W_i+c_O\mathbb E O^{(s)}=\mathrm{objective}(x).$$
--
--   This is the paper's main claim: every appointment schedule of the multi-server system can be evaluated exactly, which is what makes it possible to optimize one.
--
--   **Formalization Note** The paper has no labelled theorem; this is the exact claim of its §4 and Eq. (20).
--
--   Differences from the source:
--   - correction: printed start of the recursion S^(1) = 1 (p.12) → S^(1) = S, through Sblock; reason: the printed value is false: at s = 1, S = (-1), α = (1) it gives F_M(t) = 1 - e^t < 0
--   - reading: p_{j,(m_1,...,m_ξ)}(t) = P[(Y, Z) = (j, (m_1,...,m_ξ))] with Z a phase process (p.11) → SystemLaw: the joint law of Y and the residual services of the clients in service; reason: the model (6) has no phase process and the page does not fix slots; the Lean form determines the law of the multiset of phases, so nothing about the system law is dropped
--   - encoding: Stieltjes integral dF_{M_n}(t) in Eq. (19) → Lebesgue integral on (0, ∞) against the density α_n exp(S_n t) t_n; reason: F_{M_n} is continuous with F_{M_n}(0) = 0, so the two integrals agree
--   - encoding: ∑ E B_i in the objective through Eq. (18) → objective uses n times the phase-type mean -α S⁻¹ 𝟙; reason: this is E B_i for PH(α, S), so the objective is a function of the schedule through matrices only
--   - generalization: T is the mean service total over s (p.15), and E B_i = 1 (p.9) → every real T and any PH(α, S) with S nonsingular; reason: the paper's T and normalization are instances
--   - encoding: α holds initial probabilities; S^{-1} and finite means are used (pp.9, 10, 14) → ∑ α = 1 and IsUnit S.det are fields next to the published IsPHRep; reason: IsPHRep allows an atom at 0 and defective phases, which the source excludes; no instance of the source is lost
--   - encoding: states (j, m) and matrices ordered in blocks by j descending → a sum type of saturated and unsaturated states, indexed by i with N = s + i; reason: a Lean convention; block order does not matter to a function of states
--   - generalization: the sum over clients, Eq. (17) → each mean E W_{s+i} separately, and the sum; reason: the sum follows from the separate means, which are what p.14 derives from F_W
--   - encoding: E W_i, E M_{s+i}, E I^(s), E O^(s) and the inverses S_{s+i}^{-1}, (S_i^wait)^{-1} used without comment → Integrable and IsUnit (det) stated as conclusions; reason: the page's expectations and inverses presuppose them; stating them rules out the junk values of the Bochner integral and Matrix.inv, and no instance of the source is lost
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, §4.1-§4.2, Eqs. (11)-(19) and the displays for $F_{W_{s+i}}$, $F_{M_{s+i}}$, pp.12-15, and Eq. (20), p.17

import Mathlib
import Definitions.Def_MultiServerAppt_IsDPHSModel
import Definitions.Def_MultiServerAppt_SystemLaw
import Definitions.Def_MultiServerAppt_W
import Definitions.Def_MultiServerAppt_idle
import Definitions.Def_MultiServerAppt_overtime
import Definitions.Def_MultiServerAppt_objective

open Matrix MeasureTheory

namespace MultiServerAppt

/-- The exact evaluation of the D/PH/s appointment system, §4.1-§4.2, for every schedule. In this
order: the system law (7), (11), (12), for `0 ≤ i ≤ n - s`; the waiting-time distribution; the mean
waiting times (17); the makespan distribution and mean; the mean idle time (18); the mean overtime
(19); and the objective (20), which is thereby a function of the schedule through the matrices.
Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, §4.1-§4.2, Eqs. (11)-(19) and
the displays for `F_{W_{s+i}}`, `F_{M_{s+i}}`, pp.12-15, and Eq. (20), p.17.

**Formalization Note** `n = s + m`, and the matrices are the page's with `S^(1) = S` in place of the
misprinted `S^(1) = 1`. The paper has no labelled theorem; this is the claim of its §4. -/
theorem dphs_exact_evaluation {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {s m : ℕ} {α : ι → ℝ}
    {S : Matrix ι ι ℝ} {x : ℕ → ℝ} {B : ℕ → Ω → ℝ} (hM : IsDPHSModel P s m α S x B)
    (T cI cO : ℝ) :
    (∀ i, i ≤ m → SystemLaw P s α S x B i) ∧
    (∀ i ∈ Finset.Icc 1 m, ∀ t : ℝ, 0 ≤ t →
      P.real {ω | W s x (fun c => B c ω) (s + i) ≤ t} =
        1 - (waitAlpha α S s x i ᵥ* NormedSpace.exp (t • waitMat α S s i)) ⬝ᵥ fun _ => (1 : ℝ)) ∧
    (∀ i ∈ Finset.Icc 1 m,
      IsUnit (waitMat α S s i).det ∧
      Integrable (fun ω => W s x (fun c => B c ω) (s + i)) P ∧
      ∫ ω, W s x (fun c => B c ω) (s + i) ∂P =
        -(waitAlpha α S s x i ⬝ᵥ ((waitMat α S s i)⁻¹ *ᵥ fun _ => (1 : ℝ)))) ∧
    (∑ c ∈ Finset.Icc (s + 1) (s + m), ∫ ω, W s x (fun c => B c ω) c ∂P =
      ∑ i ∈ Finset.Icc 1 m,
        -(waitAlpha α S s x i ⬝ᵥ ((waitMat α S s i)⁻¹ *ᵥ fun _ => (1 : ℝ)))) ∧
    (∀ i ∈ Finset.Icc 1 m,
      (∀ t : ℝ, 0 ≤ t →
        P.real {ω | M s x (fun c => B c ω) (s + i) ≤ t} =
          1 - (alphaSys α S s x i ᵥ* NormedSpace.exp (t • sysMat α S s i)) ⬝ᵥ fun _ => (1 : ℝ)) ∧
      IsUnit (sysMat α S s i).det ∧
      Integrable (fun ω => M s x (fun c => B c ω) (s + i)) P ∧
      ∫ ω, M s x (fun c => B c ω) (s + i) ∂P =
        -(alphaSys α S s x i ⬝ᵥ ((sysMat α S s i)⁻¹ *ᵥ fun _ => (1 : ℝ)))) ∧
    (Integrable (fun ω => idle s x (fun c => B c ω) (s + m)) P ∧
      ∫ ω, idle s x (fun c => B c ω) (s + m) ∂P =
        (s : ℝ) * (∫ ω, M s x (fun c => B c ω) (s + m) ∂P + arr s x (s + m)) -
          ∑ c ∈ Finset.Icc 1 (s + m), ∫ ω, B c ω ∂P) ∧
    (Integrable (fun ω => overtime s x (fun c => B c ω) (s + m) T) P ∧
      ∫ ω, overtime s x (fun c => B c ω) (s + m) T ∂P =
        (s : ℝ) * ∫ t in Set.Ioi (0 : ℝ),
          max (t + arr s x (s + m) - T) 0 *
            (alphaSys α S s x m ᵥ* NormedSpace.exp (t • sysMat α S s m)) ⬝ᵥ
              MatrixAnalytic.PH.exitRates (sysMat α S s m)) ∧
    cI * ∫ ω, idle s x (fun c => B c ω) (s + m) ∂P +
        ∑ c ∈ Finset.Icc (s + 1) (s + m), ∫ ω, W s x (fun c => B c ω) c ∂P +
        cO * ∫ ω, overtime s x (fun c => B c ω) (s + m) T ∂P =
      objective α S s m x T cI cO := by sorry

end MultiServerAppt
