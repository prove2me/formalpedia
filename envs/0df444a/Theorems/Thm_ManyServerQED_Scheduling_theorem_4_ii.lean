-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_theorem_4_ii
-- name    : ManyServerQED.Scheduling.theorem_4_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:47:07.091041+00:00
-- url     : https://prove2.me/theorems/8128dd71-40e3-4748-8c84-dd3ac2183ad8
-- title:
--   Theorem 4(ii) — under (49), $\limsup_n E\int e^{-\gamma t}L(\hat X^n_t,u^n_t)\,dt\le V(x)$
-- statement:
--   In the setting of Theorem 4(i), let $f$ be a $C^2_{\mathrm{pol}}$ solution of the HJB equation (41) for the limit data. Put
--   $$
--   K^n_t=b(\hat X^n_t,u^n_t)\cdot Df(\hat X^n_t)+L(\hat X^n_t,u^n_t)-H(\hat X^n_t,Df(\hat X^n_t))\ \ge0.\qquad(48)
--   $$
--   If
--   $$
--   \int_0^\cdot e^{-\gamma s}K^n_s\,ds\Rightarrow0,\qquad(49)
--   $$
--   then
--   $$
--   \limsup_{n\to\infty}E\int_0^\infty e^{-\gamma t}L(\hat X^n_t,u^n_t)\,dt\le V(x).
--   $$
--
--   Condition (49) says that the policies asymptotically follow minimizers of the Hamiltonian. The proof of Theorem 2 checks it for the proposed policy.
--
--   **Formalization Note** The limit in (49) is the zero process, so weak convergence is convergence uniformly on compacts in probability (`UocInProb`). $f$ is hypothesized; by Theorem 3 it exists and is the unique $C^2_{\mathrm{pol}}$ solution, as the paper's "the unique $C^2_{\mathrm{pol}}$ solution" presumes. The limsup is taken in $[0,\infty]$.
-- source:
--   Atar, Mandelbaum & Reiman, Scheduling a Multi Class Queue with Many Exponential Servers: Asymptotic Optimality in Heavy Traffic, arXiv:math/0407058v1 (reprint of Ann. Appl. Probab. 14(3), 2004), p. 31, (48)-(49) and Theorem 4(ii)

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_ManyServerQED_Scheduling_Diffusion
import Definitions.Def_ManyServerQED_Scheduling_Model
import Definitions.Def_ManyServerQED_Scheduling_Policy

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ManyServerQED.Scheduling

open BellWilliams2001.ThresholdPolicy

/-- Theorem 4(ii) (p. 31): in the setting of Theorem 4(i), let `f` be the `C²_pol` solution of (41)
and `Kⁿ_t = b(X̂ⁿ_t, uⁿ_t) · Df(X̂ⁿ_t) + L(X̂ⁿ_t, uⁿ_t) − H(X̂ⁿ_t, Df(X̂ⁿ_t))` (48). If (49)
`∫₀^· e^{−γs}Kⁿ_s ds ⇒ 0` holds, then `limsup_n E ∫₀^∞ e^{−γt} L(X̂ⁿ_t, uⁿ_t) dt ≤ V(x)`. -/
theorem theorem_4_ii {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} [NeZero k] (M : SystemSequence Ω k)
    (Lt : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (ϱ mL mU γ : ℝ)
    (hA2 : Assumption2 Lt ϱ mL) (hA3 : M.Assumption3 mL mU) (hγ : 0 < γ)
    (u0 : Fin k → ℝ) (hu0 : u0 ∈ stdSimplex ℝ (Fin k))
    (X0 : ℕ → Fin k → ℕ) (x : Fin k → ℝ)
    (hX0 : Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x))
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ)
    (hpol : ∀ n, 1 ≤ n → M.IsSCP n (X0 n) (X n) (Ψ n) ∧ M.IsAdmissible n (X n) (Ψ n) ∧
      IsWorkConserving n (X n) (Ψ n))
    (f : (Fin k → ℝ) → ℝ) (hf : IsC2Pol f)
    (hHJB : IsHJBSolution M.diffData (costOfTilde Lt) γ f)
    (h49 : UocInProb M.P
      (fun n ω t => ![∫ s in (0 : ℝ)..t, Real.exp (-γ * s) *
        (∑ i, drift M.diffData (M.Xhat n (X n) ω s) (uProc n u0 (X n) (Ψ n) ω s) i *
            grad f (M.Xhat n (X n) ω s) i +
          costOfTilde Lt (M.Xhat n (X n) ω s) (uProc n u0 (X n) (Ψ n) ω s) -
          hamiltonian M.diffData (costOfTilde Lt) (M.Xhat n (X n) ω s)
            (grad f (M.Xhat n (X n) ω s)))])
      (fun _ => 0)) :
    limsup (fun n => M.queueCostL (costOfTilde Lt) γ n u0 (X n) (Ψ n)) atTop ≤
      value M.diffData (costOfTilde Lt) γ x := by sorry

end ManyServerQED.Scheduling
