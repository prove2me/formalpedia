-- Prove2me | Theorems.Thm_JSEQDelay_Diffusion_lemma_3_10
-- name    : JSEQDelay.Diffusion.lemma_3_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:19:00.488054+00:00
-- url     : https://prove2.me/theorems/1964d3bd-c39f-49e9-9499-07811b83567e
-- title:
--   Lemma 3.10 (corrected: η uniform in T), p. 15 — Example 3 estimators satisfy Assumptions 3.5, 3.8 and 3.9
-- statement:
--   Let $\tau$ be a delay function and let $h:\mathbb R_+\times\mathbb R_+^K\times\mathbb R^K\to\mathbb R_+^K$ satisfy $h(0,0,0)=0$ and condition (34) with **one** constant $\eta\in[0,1)$ for all $T$: for each $T$ there is a non-decreasing continuous $\kappa:[0,T]\to\mathbb R_+$, $\kappa(0)=0$, with
--   $$|h_k(t,v,u)-h_k(t',v',u')|\le\kappa(|t-t'|)+|v_k-v'_k|+\eta|u_k-u'_k|$$
--   for $t,t'\in[0,T]$, $v,v'\in\mathbb R_+^K$, $u,u'\in\mathbb R^K$. Define $\Psi^n$ by (35) and $\hat\Psi$ by (36). Then the scaled estimators $\hat\Psi^n$ and $\hat\Psi$ satisfy Assumptions 3.5, 3.8 and 3.9.
--
--   The lemma shows that the hypotheses of Theorem 4.4 are met by a rich class of estimators, including the delayed-queue-length estimator ($h\equiv0$) and the estimators of §7.
--
--   **Formalization Note** As printed, Example 3 lets $\eta$ depend on $T$, and the lemma is then false: for $\tau\equiv0$ and $h_k(t,v,u)=\frac{t}{1+t}\min(u_k^+,1)$, (34) holds with $\eta_T=T/(1+T)$, yet (37) would force $t_0/(1+t_0)\le\zeta_1<1$ for every $t_0$. The statement takes $\eta$ uniform in $T$, which is what the proof in Appendix B.1 uses ($\zeta_1=\zeta_2=\eta$, $o=\kappa(\delta)$). The rates $\mu^n$ are arbitrary: they cancel in the scaled estimator.
-- source:
--   Atar & Lipshutz, Heavy traffic limits for join the shortest estimated queue policy using delayed information, authors' manuscript of January 12, 2020 (Math. Oper. Res. 46(3), 2021, doi:10.1287/moor.2020.1056), p. 15, Lemma 3.10; Example 3, pp. 12–13, (34)–(36); proof in Appendix B.1, p. 37

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_RankBasedSDI_LoadBalancing_CTight
import Definitions.Def_JSEQDelay_Diffusion_Model
import Definitions.Def_JSEQDelay_Diffusion_Assumptions
import Definitions.Def_JSEQDelay_Diffusion_Example3

namespace JSEQDelay.Diffusion

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open BellWilliams2001.ThresholdPolicy RankBasedSDI.LoadBalancing

/-- **Lemma 3.10** (p. 15), **corrected: `η` uniform in `T`**. Let `h : ℝ₊ × ℝ₊^K × ℝ^K → ℝ₊^K`
satisfy the conditions of Example 3 with one constant `η ∈ [0, 1)` for all `T` (the page lets
`η` depend on `T`, and the lemma then fails). Let the estimators `Ψⁿ` be defined by (35) and
`Ψ̂` by (36). Then Assumptions 3.5, 3.8 and 3.9 hold. -/
theorem lemma_3_10 {K : ℕ} (hK : 2 ≤ K)
    (τ : ℝ → Fin K → ℝ) (hτ : DelayFunction τ) (mu : ℕ → Fin K → ℝ)
    (h : ℝ → (Fin K → ℝ) → (Fin K → ℝ) → Fin K → ℝ) (hh : Example3Uniform h) :
    Assumption35 (fun n => PsiHat n (mu n) (ex3Psi n (mu n) τ h)) (ex3PsiLim τ h) ∧
    Assumption38 τ (fun n => PsiHat n (mu n) (ex3Psi n (mu n) τ h)) ∧
    Assumption39 τ (ex3PsiLim τ h) := by sorry

end JSEQDelay.Diffusion
