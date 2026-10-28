-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_directional_centeredGradient_logLaplace_zero_of_compact_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.directional_centeredGradient_logLaplace_zero_of_compact_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:07.364211+00:00
-- url     : https://prove2.me/theorems/9f51014f-22c8-44a0-ab77-cef40f1a23ab
-- title:
--   Directional Cumulants of the Centered Log-Laplace Gradient
-- statement:
--   This is a finite-dimensional directional-derivative identity for a centered log-Laplace gradient.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel measurable structure, and let $\mu$ be a compactly supported probability measure on $E$. For every finite list $l$ of vectors in $E$, set $\Lambda=\log\operatorname{Laplace}(\mu)$. The directional derivative indexed by $l$ of $z\mapsto\nabla\Lambda(z)-\nabla\Lambda(0)$ at $0$ is zero when $l$ is empty, and otherwise is the cumulant vector associated with $l$:
--
--   $$\operatorname{directional}\,l\,(\nabla\Lambda-\nabla\Lambda(0))(0)=
--   \begin{cases}0,&l=[]\\
--   \operatorname{cumulantVector}(\mu,l),&l\ne[].
--   \end{cases}$$
--
--   This result packages the corresponding iterated-derivative identity in list form for reuse in multilinear expansions.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem directional_centeredGradient_logLaplace_zero_of_compact (μ : ProbabilityMeasure E)
--       (hc : IsCompact (μ : Measure E).support) (l : List E) :
--       directional l (fun z : E =>
--           gradient (logLaplace (μ : Measure E)) z - gradient (logLaplace (μ : Measure E)) 0) 0 =
--         if l = [] then 0 else cumulantVector (μ : Measure E) l
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Cumulant/Leibniz`](https://prove2.me/theorems/dc69b9b3-3173-4efb-aee3-b6d1282be46f).
--
--   Definition modules: [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598), [`Analysis/BakryEmery/Cumulant/Local`](https://prove2.me/theorems/7a0cd01c-3ad0-460b-af3d-e088447d401d), [`Analysis/IteratedDerivative/Symmetry`](https://prove2.me/theorems/c3281ab2-65ad-4ae5-995a-70d685aba1dc).
--
--   Supporting theorems: [`iteratedFDeriv_centeredGradient_logLaplace_zero_of_compact`](https://prove2.me/theorems/c850afc5-a923-4019-b001-39ff0f56dd9b).
--
--   Next: [`iteratedFDeriv_inner_centeredGradient_zero_of_compact`](https://prove2.me/theorems/51587601-8a8b-458d-95cb-37b7054bab4d).
--
--   [Source excerpt, lines 30–34](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Leibniz.lean#L30-L34) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Theorem 4.1, p. 18. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Leibniz.lean#L29-L58 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Leibniz`, declaration `FunctionalInequalities.Analysis.BakryEmery.directional_centeredGradient_logLaplace_zero_of_compact`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Leibniz

open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.BakryEmery.directional_centeredGradient_logLaplace_zero_of_compact_readable (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (l : List E) :
    directional l (fun z : E =>
        gradient (logLaplace (μ : Measure E)) z - gradient (logLaplace (μ : Measure E)) 0) 0 =
      if l = [] then 0 else cumulantVector (μ : Measure E) l := by sorry
