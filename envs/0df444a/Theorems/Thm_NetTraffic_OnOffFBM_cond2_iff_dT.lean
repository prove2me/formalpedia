-- Prove2me | Theorems.Thm_NetTraffic_OnOffFBM_cond2_iff_dT
-- name    : NetTraffic.OnOffFBM.cond2_iff_dT
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:03:26.925189+00:00
-- url     : https://prove2.me/theorems/3de1d5bf-b677-4d90-a323-5378f04cc609
-- title:
--   §7, p. 61 — Condition 2 ⇔ T = o(d_T), since d_T/T = [M T F̄_on(T)]^{1/2}
-- statement:
--   Let $F_{\mathrm{on}}$, $F_{\mathrm{off}}$ satisfy (2.1)–(2.2), let the number of sources $M=M(T)$ be integer valued, non-decreasing, with $M(T)\to\infty$, and let $d_T=[T^{3-\alpha}L_{\mathrm{on}}(T)M]^{1/2}$ with $L_{\mathrm{on}}(T)=T^\alpha\bar F_{\mathrm{on}}(T)$. Then Fast Growth Condition 2, $b(MT)/T\to\infty$, holds if and only if
--   $$\frac{T}{d_T}\to0\qquad(T\to\infty),$$
--   and for every $T>0$,
--   $$\frac{d_T}{T}=[MT\bar F_{\mathrm{on}}(T)]^{1/2}.$$
--
--   The equivalence is Lemma 1 of the paper with $M$ in place of $\lambda$ (§3.2): Condition 2 is the same as $MT\bar F_{\mathrm{on}}(T)\to\infty$. In this form the condition says that the normalisation $d_T$ of the cumulative input dominates the time scale $T$, which is what makes single sources negligible in Lemma 13.
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), p. 61, §7, d_T and the sentence 'By Lemma 1, Condition 2 is equivalent to o(d_T) = T'; Lemma 1, p. 30, and §3.2, p. 32

import Mathlib
import Definitions.Def_NetTraffic_OnOffFBM_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace NetTraffic.OnOffFBM

/-- §7, p. 61: by Lemma 1 (with `M` for `λ`), Condition 2 is equivalent to `T = o(d_T)`,
since `d_T/T = [M T F̄_on(T)]^{1/2}`. -/
theorem cond2_iff_dT
    (Fon Foff : Measure ℝ) [IsProbabilityMeasure Fon] [IsProbabilityMeasure Foff]
    (α αoff : ℝ) (hF : HeavyTails Fon Foff α αoff)
    (M : ℝ → ℕ) (hM : SourceCount M) :
    (Condition2 Fon M ↔ Tendsto (fun T => T / dT Fon α M T) atTop (𝓝 0)) ∧
      ∀ T : ℝ, 0 < T → dT Fon α M T / T = Real.sqrt ((M T : ℝ) * T * Fbar Fon T) := by sorry

end NetTraffic.OnOffFBM
