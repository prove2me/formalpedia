-- Prove2me | Theorems.Thm_OTSensitivity_Info_eq_66
-- name    : OTSensitivity.Info.eq_66
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:14:52.53998+00:00
-- url     : https://prove2.me/theorems/60eda95f-a471-4d7e-8b65-a9b1d198bad7
-- title:
--   (66) — the conditional law given 𝓕 is the µ^𝓕-mixture of the conditional laws given X
-- statement:
--   Let $(\Omega,\mathcal B,\mathbb P)$ be a probability space, $\mathsf X,\mathsf Y$ Polish spaces, and $X:\Omega\to\mathsf X$, $Y:\Omega\to\mathsf Y$ measurable, with $\mu$ the law of $X$. Let $\mathcal F\subseteq\mathscr B(\mathsf X)$ be a sub-σ-algebra. Let
--
--   1. $(\nu_x)_{x\in\mathsf X}$ be a version of the conditional distribution of $Y$ given $X$ (that is, given $(X,\mathscr B(\mathsf X))$);
--   2. $(\nu^{\mathcal F}_{x'})_{x'\in\mathsf X}$ be a version of the conditional distribution of $Y$ given $(X,\mathcal F)$;
--   3. $(\mu^{\mathcal F}_{x'})_{x'\in\mathsf X}$ be a disintegration of $\mu$ with respect to $\mathcal F$: probability measures on $\mathsf X$ with $x'\mapsto\mu^{\mathcal F}_{x'}(C)$ $\mathcal F$-measurable and $\mu(A\cap C)=\int_A\mu^{\mathcal F}_{x'}(C)\,d\mu(x')$ for $A\in\mathcal F$ and Borel $C$.
--
--   Then
--   $$\nu^{\mathcal F}_{x'}=\int_{\mathsf X}\nu_x\,d\mu^{\mathcal F}_{x'}(x)\qquad\text{for }\mu\text{-a.e. }x'\in\mathsf X.$$
--
--   This mixture formula is the first step of the proof of Theorem 8: combined with the convexity of $K(\nu,\cdot)$ it gives $\xi^K(Y,X\mid\mathcal F)\le\xi^K(Y,X)$.
--
--   **Formalization Note** The paper writes "the disintegration of $\pi$ w.r.t. $X$ and the σ-algebra $\mathcal F$", where $\pi$ is the joint law of $(X,Y)$, a symbol not introduced in §3; this is the conditional distribution of $Y$ given $(X,\mathcal F)$. The disintegration $\mu^{\mathcal F}$ is encoded as a version of the conditional distribution of the identity of $(\mathsf X,\mu)$ given $\mathcal F$. The mixture $\int\nu_x\,d\mu^{\mathcal F}_{x'}(x)$ is `Measure.bind`. The identity is an equality of measures, for every choice of the three versions.
-- source:
--   Borgonovo, Figalli, Plischke & Savaré, Global Sensitivity Analysis via Optimal Transport, authors' manuscript of 7 March 2024 (Management Science, doi:10.1287/mnsc.2023.01796), Appendix A, proof of Theorem 8, (66)–(67), p. 35

import Mathlib
import Definitions.Def_OTSensitivity_Info_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace OTSensitivity.Info

/-- (66), proof of Theorem 8, p. 35: the conditional law of `Y` given the coarser information
`(X, 𝓕)` is, for `µ`-a.e. `x'`, the mixture of the conditional laws `ν_x` of `Y` given `X` against the
disintegration `µ^𝓕_x'` of `µ` (the law of `X`) with respect to `𝓕`. The disintegration is any
version of the conditional law of the identity map of `(𝓧, µ)` given `𝓕`. -/
theorem eq_66 {Ω 𝓧 𝓨 : Type*} [MeasurableSpace Ω] (F : MeasurableSpace 𝓧)
    [TopologicalSpace 𝓧] [PolishSpace 𝓧] [m𝓧 : MeasurableSpace 𝓧] [BorelSpace 𝓧]
    [TopologicalSpace 𝓨] [PolishSpace 𝓨] [MeasurableSpace 𝓨] [BorelSpace 𝓨]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → 𝓧) (Y : Ω → 𝓨) (hX : Measurable X) (hY : Measurable Y)
    (hF : F ≤ m𝓧)
    (κ : Kernel 𝓧 𝓨) (hκ : IsCondDistrib P X Y m𝓧 κ)
    (κF : Kernel 𝓧 𝓨) (hκF : IsCondDistrib P X Y F κF)
    (μF : Kernel 𝓧 𝓧) (hμF : IsCondDistrib (P.map X) id id F μF) :
    ∀ᵐ x' ∂(P.map X), κF x' = (μF x').bind κ := by sorry

end OTSensitivity.Info
