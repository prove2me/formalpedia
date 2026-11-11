-- Prove2me | Theorems.Thm_LogSupermodularBIS_Main_lemma_3_2
-- name    : LogSupermodularBIS.Main.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:33:50.385891+00:00
-- url     : https://prove2.me/theorems/5e86b230-1035-40f8-8e70-6269b862d620
-- title:
--   Lemma 3.2 — bathtub principle for the logit
-- statement:
--   Let $a(u)=\log(u/(1-u))$ and let $H$ be the binary entropy. If $\phi:(0,1)\to[0,1]$ is measurable and $\int_0^1\phi=p$, then
--   $$\int_0^1a\phi\le H(p),$$
--   with equality only if $\phi=\mathbf 1_{[1-p,1)}$ almost everywhere.
--
--   This is the step-by-step rearrangement inequality behind the Boolean-guide variational principle.
--
--   Differences from the source:
--   - encoding: measurable ϕ : (0,1) → [0,1] → measurable ϕ : ℝ → ℝ with values in [0,1] on (0,1); all integrals over (0,1); reason: only the values on (0,1) enter
-- source:
--   Jingcheng Liu, Yitong Yin, STOC 2027 submission #1385 (October 2026), p. 14 (PDF 15), Lemma 3.2

import Definitions.Def_LogSupermodularBIS_Main_Interaction

open MeasureTheory

set_option autoImplicit false

namespace LogSupermodularBIS.Main

/-- Lemma 3.2 (Bathtub principle), p. 14. -/
theorem lemma_3_2 (ϕ : ℝ → ℝ) (hϕ : Measurable ϕ)
    (hrange : ∀ u ∈ Set.Ioo (0 : ℝ) 1, ϕ u ∈ Set.Icc (0 : ℝ) 1) (p : ℝ)
    (hp : ∫ u in Set.Ioo (0 : ℝ) 1, ϕ u = p) :
    (∫ u in Set.Ioo (0 : ℝ) 1, logit u * ϕ u) ≤ H p ∧
    ((∫ u in Set.Ioo (0 : ℝ) 1, logit u * ϕ u) = H p →
      ∀ᵐ u ∂((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)),
        ϕ u = if 1 - p ≤ u then 1 else 0) := by sorry

end LogSupermodularBIS.Main
