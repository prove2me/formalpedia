-- Prove2me | Theorems.Thm_OTSensitivity_Info_ae_weak_convergence
-- name    : OTSensitivity.Info.ae_weak_convergence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:15:06.448092+00:00
-- url     : https://prove2.me/theorems/c7d15589-9435-4ad0-afd2-8430cf3029ca
-- title:
--   Proof of Theorem 9 — ν^n_x → ν^∞_x weakly for µ-a.e. x
-- statement:
--   Let $(\Omega,\mathcal B,\mathbb P)$ be a probability space, $\mathsf X,\mathsf Y$ Polish spaces, $X:\Omega\to\mathsf X$ and $Y:\Omega\to\mathsf Y$ measurable with $\mu$ the law of $X$. Let $(\mathcal F_n)_{n}$ be an increasing sequence of sub-σ-algebras of $\mathscr B(\mathsf X)$ and $\mathcal F=\bigvee_n\mathcal F_n$ the smallest σ-algebra containing every $\mathcal F_n$. Let $\nu^n_x$ be a version of the conditional distribution of $Y$ given $(X,\mathcal F_n)$, for each $n$, and $\nu^\infty_x$ a version of the conditional distribution of $Y$ given $(X,\mathcal F)$. Then for $\mu$-a.e. $x\in\mathsf X$, $\nu^n_x\to\nu^\infty_x$ weakly:
--   $$\lim_{n\to\infty}\int_{\mathsf Y}\varphi\,d\nu^n_x=\int_{\mathsf Y}\varphi\,d\nu^\infty_x\qquad\text{for every }\varphi\in C_b(\mathsf Y).$$
--
--   This is the martingale-convergence step of the proof of Theorem 9; the exceptional null set does not depend on $\varphi$.
--
--   **Formalization Note** Weak convergence is expressed by testing against all bounded continuous real functions ($\mathsf Y\to^b\mathbb R$). The sequence is indexed by $n\in\mathbb N=\{0,1,\dots\}$ rather than from $1$. The versions for different $n$ are arbitrary and need not be compatible.
-- source:
--   Borgonovo, Figalli, Plischke & Savaré, Global Sensitivity Analysis via Optimal Transport, authors' manuscript of 7 March 2024 (Management Science, doi:10.1287/mnsc.2023.01796), Appendix A, proof of Theorem 9, p. 36

import Mathlib
import Definitions.Def_OTSensitivity_Info_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace OTSensitivity.Info

/-- Proof of Theorem 9, p. 36: along an increasing sequence of sub-σ-algebras `𝓕ₙ` of `𝓑(𝓧)` with
join `𝓕`, the conditional laws `ν^n_x` of `Y` given `(X, 𝓕ₙ)` converge weakly to the conditional law
`ν^∞_x` of `Y` given `(X, 𝓕)` for `µ`-a.e. `x`. Weak convergence is tested against every bounded
continuous `φ : 𝓨 → ℝ`. -/
theorem ae_weak_convergence {Ω 𝓧 𝓨 : Type*} [MeasurableSpace Ω] (Fs : ℕ → MeasurableSpace 𝓧)
    [TopologicalSpace 𝓧] [PolishSpace 𝓧] [m𝓧 : MeasurableSpace 𝓧] [BorelSpace 𝓧]
    [TopologicalSpace 𝓨] [PolishSpace 𝓨] [MeasurableSpace 𝓨] [BorelSpace 𝓨]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → 𝓧) (Y : Ω → 𝓨) (hX : Measurable X) (hY : Measurable Y)
    (hmono : Monotone Fs) (hle : ∀ n, Fs n ≤ m𝓧)
    (κs : ℕ → Kernel 𝓧 𝓨) (hκs : ∀ n, IsCondDistrib P X Y (Fs n) (κs n))
    (κ : Kernel 𝓧 𝓨) (hκ : IsCondDistrib P X Y (⨆ n, Fs n) κ) :
    ∀ᵐ x ∂(P.map X), ∀ φ : 𝓨 →ᵇ ℝ,
      Tendsto (fun n => ∫ y, φ y ∂(κs n x)) atTop (𝓝 (∫ y, φ y ∂(κ x))) := by sorry

end OTSensitivity.Info
