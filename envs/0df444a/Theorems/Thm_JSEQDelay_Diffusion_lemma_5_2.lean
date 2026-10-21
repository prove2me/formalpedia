-- Prove2me | Theorems.Thm_JSEQDelay_Diffusion_lemma_5_2
-- name    : JSEQDelay.Diffusion.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:19:03.828757+00:00
-- url     : https://prove2.me/theorems/1fad6e4f-f6d2-4514-ba0d-cd2aaf9cdaed
-- title:
--   Lemma 5.2, p. 18 — the processes (Âⁿ, Q̂ⁿ, L̂ⁿ, M̂ⁿ) stopped at θⁿ are C-tight
-- statement:
--   Assume the primitives, heavy traffic, Assumption 3.1 on the delay function, and Assumption 3.8 on the scaled estimators $\hat\Psi^n$, and let $(Q^n,A^n)$ be the JSEQ networks. Let $(r_n)$ be positive with $r_n\to0$ and $\theta^n=\inf\{t\ge0:\hat\Delta^n(t)\ge r_n\}$ as in (47). Then the sequence of stopped processes
--   $$\big(\hat A^n(\cdot\wedge\theta^n),\hat Q^n(\cdot\wedge\theta^n),\hat L^n(\cdot\wedge\theta^n),\hat M^n(\cdot\wedge\theta^n)\big)_{n\ge1}$$
--   is C-tight in $\mathbb D(\mathbb R^{4K})$.
--
--   Before the gap $\hat\Delta^n$ between the largest estimate and the average reaches $r_n$, routing keeps the estimates together; the lemma turns this into tightness with continuous limits.
--
--   **Formalization Note** C-tightness is the published `IsCTight`, which bounds $\sup_{[0,t]}|Y^n|$ where Definition 3.7 bounds $|Y^n(0)|$; the two agree under the modulus condition because $\sup_{[0,T]}|Y|\le|Y(0)|+(T/\delta+1)w(Y,\delta,T)$, and here every process starts at $0$. The four processes are concatenated into one $4K$-dimensional process, so their tightness is joint. The printed display has an unbalanced parenthesis, kept in the quotation.
-- source:
--   Atar & Lipshutz, Heavy traffic limits for join the shortest estimated queue policy using delayed information, authors' manuscript of January 12, 2020 (Math. Oper. Res. 46(3), 2021, doi:10.1287/moor.2020.1056), p. 18, Lemma 5.2, with (46)–(47)

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_RankBasedSDI_LoadBalancing_CTight
import Definitions.Def_JSEQDelay_Diffusion_Model
import Definitions.Def_JSEQDelay_Diffusion_Assumptions
import Definitions.Def_JSEQDelay_Diffusion_Collapse

namespace JSEQDelay.Diffusion

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open BellWilliams2001.ThresholdPolicy RankBasedSDI.LoadBalancing

/-- **Lemma 5.2** (p. 18): under Assumption 3.1 on the delay function and the modulus of
continuity condition Assumption 3.8 on the scaled estimators `Ψ̂ⁿ`, for every `(rₙ) ∈ 𝒵`
(positive reals converging to `0`), with `θⁿ = inf{t ≥ 0 : Δ̂ⁿ(t) ≥ rₙ}` (47), the stopped
processes `(Âⁿ(· ∧ θⁿ), Q̂ⁿ(· ∧ θⁿ), L̂ⁿ(· ∧ θⁿ), M̂ⁿ(· ∧ θⁿ))` form a C-tight sequence. -/
theorem lemma_5_2 {K : ℕ} (hK : 2 ≤ K)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (u : ℕ → Ω → ℝ) (v : Fin K → ℕ → Ω → ℝ) (α : ℝ) (γ : Fin K → ℝ)
    (hprim : Primitives P u v α γ)
    (lam : ℕ → ℝ) (mu : ℕ → Fin K → ℝ) (lamBar lamHat : ℝ) (muBar muHat : Fin K → ℝ)
    (hrates : Rates lam mu) (hHT : HeavyTraffic lam mu lamBar lamHat muBar muHat)
    (τ : ℝ → Fin K → ℝ) (hτ : Assumption31 τ)
    (Ψ : ℕ → Path K → Path K → Path K) (hΨ : ∀ n, IsEstimator τ (Ψ n))
    (h38 : Assumption38 τ (fun n => PsiHat n (mu n) (Ψ n)))
    (Q A : ℕ → Ω → Path K)
    (hnet : ∀ n, 1 ≤ n → IsJSEQNetwork u v (lam n) (mu n) τ (Ψ n) (Q n) (A n))
    (r : ℕ → ℝ) (hr_pos : ∀ n, 0 < r n) (hr_lim : Tendsto r atTop (𝓝 0)) :
    IsCTight P (fun n ω => stopAt
      (theta (r n) (Delta n (mu n) τ (Ψ n) (Q n) (A n)) ω)
      (quad n (mu n) (Ψ n) (Q n) (A n) ω)) := by sorry

end JSEQDelay.Diffusion
