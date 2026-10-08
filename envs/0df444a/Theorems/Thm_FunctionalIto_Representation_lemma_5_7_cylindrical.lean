-- Prove2me | Theorems.Thm_FunctionalIto_Representation_lemma_5_7_cylindrical
-- name    : FunctionalIto.Representation.lemma_5_7_cylindrical
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:22.717756+00:00
-- url     : https://prove2.me/theorems/1cec18ba-9526-4d89-b276-4c5f960694b4
-- title:
--   Lemma 5.7 (proof), p. 18 — the cylindrical integral has a regular functional representation with the stated derivatives
-- statement:
--   Let $n\ge1$, $0\le t_1<\dots<t_n\le T$, and let $f:(\mathbb R^d)^n\to\mathbb R^d$ be infinitely differentiable and bounded with all its derivatives ($f\in C_b^\infty$). Define the nonanticipative functional
--   $$F_t(x_t,v_t)=f\big(x(t_1-),\dots,x(t_n-)\big)\cdot\big(x(t)-x(t_n)\big)\,1_{t>t_n}.$$
--   Then $F\in\mathbb C_b^{1,2}([0,T))$, $F$ verifies (10), and
--   $$\nabla_xF_t(x_t,v_t)=f\big(x(t_1-),\dots,x(t_n-)\big)1_{t>t_n},\qquad\nabla_x^2F_t(x_t,v_t)=0,\qquad\mathcal D_tF(x_t,v_t)=0.$$
--
--   Under Assumption 5.1, the process $Y(t)=F_t(X_t,A_t)$ is the Itô integral of the cylindrical integrand $f(X(t_1),\dots,X(t_n))1_{t>t_n}$ against $X$. This identity and the derivative calculations supply the test processes used in the density proof of Lemma 5.7.
--
--   **Formalization Note.** The $n$ times are indexed by $\{0,\dots,n'\}$ with $n=n'+1\ge1$, and $t_n$ is the last one. For $d>1$, $f$ is $\mathbb R^d$-valued and the product is the dot product (the page writes the case $d=1$). $x(t_i-)$ is the left limit, equal to $x(0)$ when $t_i=0$. The derivatives are witnesses of the class $\mathbb C_b^{1,2}$. The stochastic identity uses the square-integrable Itô integral in the Brownian setting, including the disclosed finite-energy assumption.
-- source:
--   Cont and Fournié, Functional Itô calculus and stochastic integral representation of martingales, arXiv:1002.2446v5, p. 18, proof of Lemma 5.7, "where the functional F is defined on Υ as … which shows that F ∈ ℂ_b^{1,2}"

import Mathlib
import Definitions.Def_auto_M05_f3f59_EthierKurtz_HasCrossVariation
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_FunctionalIto_Representation_Setting
import Definitions.Def_FunctionalIto_Representation_L2

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators Matrix

namespace FunctionalIto.Representation

theorem lemma_5_7_cylindrical {d n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ≥0)
    (W : ℝ≥0 → Ω → EthierKurtz.SDEState d)
    (𝒢 ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (σ : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ)
    (X : ℝ≥0 → Ω → (Fin d → ℝ))
    (A : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ)
    (hS : IsBrownianSetting P T W 𝒢 σ X ℱ A)
    (ts : Fin (n + 1) → ℝ≥0)
    (hts : StrictMono ts) (hT : ts (Fin.last n) ≤ T)
    (f : (Fin (n + 1) → Fin d → ℝ) → (Fin d → ℝ))
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hfb : ∀ k : ℕ, ∃ C : ℝ, ∀ y, ‖iteratedFDeriv ℝ k f y‖ ≤ C) :
    IsC12b T (cylindricalF ts f) 0 (cylindricalGradF ts f) 0 ∧
      PredictableInV T (cylindricalF ts f) ∧
      IsItoIntegral P ℱ T X A
        (fun t ω => cylindricalGradF ts f t (fun s => X s ω) (fun s => A s ω))
        (fun t ω => cylindricalF ts f t (fun s => X s ω) (fun s => A s ω)) := by sorry

end FunctionalIto.Representation
