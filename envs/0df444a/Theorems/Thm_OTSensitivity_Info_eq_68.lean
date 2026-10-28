-- Prove2me | Theorems.Thm_OTSensitivity_Info_eq_68
-- name    : OTSensitivity.Info.eq_68
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:15:03.549928+00:00
-- url     : https://prove2.me/theorems/d31ce266-fc36-4c86-8cc3-84135a6448a1
-- title:
--   (68) — the conditional law given U = g(X) is the µ_u-mixture of the conditional laws given X
-- statement:
--   Let $(\Omega,\mathcal B,\mathbb P)$ be a probability space, $\mathsf X,\mathsf Y,\mathsf U$ Polish spaces, $X:\Omega\to\mathsf X$ and $Y:\Omega\to\mathsf Y$ measurable with $\mu$ the law of $X$, and $g:\mathsf X\to\mathsf U$ a Borel map. Put $U=g\circ X$ and $\sigma=g_\sharp\mu$, the law of $U$. Let
--
--   1. $(\nu_x)_{x\in\mathsf X}$ be a version of the conditional distribution of $Y$ given $X$;
--   2. $(\nu'_u)_{u\in\mathsf U}$ be a version of the conditional distribution of $Y$ given $U$;
--   3. $(\mu_u)_{u\in\mathsf U}$ be a disintegration of $\mu$ along $g$: probability measures on $\mathsf X$, measurable in $u$, with $\mu(g^{-1}(A)\cap C)=\int_A\mu_u(C)\,d\sigma(u)$ for Borel $A\subseteq\mathsf U$, $C\subseteq\mathsf X$.
--
--   Then
--   $$\nu'_u=\int_{\mathsf X}\nu_x\,d\mu_u(x)\qquad\text{for }\sigma\text{-a.e. }u\in\mathsf U.$$
--
--   This is the mixture formula used for (24) in the proof of Theorem 8.
--
--   **Formalization Note** The paper's "disintegration of $\pi$ given $g$" is the conditional distribution of $Y$ given $U=g(X)$. The disintegration $\mu_u$ is encoded as a version of the conditional distribution of the identity of $(\mathsf X,\mu)$ given $g$. The identity holds for every choice of the three versions.
-- source:
--   Borgonovo, Figalli, Plischke & Savaré, Global Sensitivity Analysis via Optimal Transport, authors' manuscript of 7 March 2024 (Management Science, doi:10.1287/mnsc.2023.01796), Appendix A, proof of Theorem 8, (68), p. 35

import Mathlib
import Definitions.Def_OTSensitivity_Info_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace OTSensitivity.Info

/-- (68), proof of Theorem 8, p. 35: for a Borel map `g : 𝓧 → 𝓤` into a Polish space and
`U = g ∘ X`, the conditional law `ν'_u` of `Y` given `U = u` is, for `σ`-a.e. `u` (`σ = g♯µ`, the law
of `U`), the mixture of the conditional laws `ν_x` of `Y` given `X` against the disintegration `µ_u`
of `µ` along `g`. The disintegration is any version of the conditional law of the identity map of
`(𝓧, µ)` given `g`. -/
theorem eq_68 {Ω 𝓧 𝓨 𝓤 : Type*} [MeasurableSpace Ω]
    [TopologicalSpace 𝓧] [PolishSpace 𝓧] [m𝓧 : MeasurableSpace 𝓧] [BorelSpace 𝓧]
    [TopologicalSpace 𝓨] [PolishSpace 𝓨] [MeasurableSpace 𝓨] [BorelSpace 𝓨]
    [TopologicalSpace 𝓤] [PolishSpace 𝓤] [m𝓤 : MeasurableSpace 𝓤] [BorelSpace 𝓤]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → 𝓧) (Y : Ω → 𝓨) (hX : Measurable X) (hY : Measurable Y)
    (g : 𝓧 → 𝓤) (hg : Measurable g)
    (κ : Kernel 𝓧 𝓨) (hκ : IsCondDistrib P X Y m𝓧 κ)
    (κU : Kernel 𝓤 𝓨) (hκU : IsCondDistrib P (g ∘ X) Y m𝓤 κU)
    (μg : Kernel 𝓤 𝓧) (hμg : IsCondDistrib (P.map X) g id m𝓤 μg) :
    ∀ᵐ u ∂(P.map (g ∘ X)), κU u = (μg u).bind κ := by sorry

end OTSensitivity.Info
