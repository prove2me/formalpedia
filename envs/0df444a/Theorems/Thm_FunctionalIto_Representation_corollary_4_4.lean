-- Prove2me | Theorems.Thm_FunctionalIto_Representation_corollary_4_4
-- name    : FunctionalIto.Representation.corollary_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:21:15.964711+00:00
-- url     : https://prove2.me/theorems/96664a14-a031-4164-ae58-cd1d38758431
-- title:
--   Corollary 4.4, p. 14 — the vertical derivative of a process is intrinsic: ᵗ[∇F¹ − ∇F²] A(t−) [∇F¹ − ∇F²] = 0 (39)
-- statement:
--   Let $X$ be a continuous $\mathbb R^d$-valued semimartingale on a filtered probability space satisfying the usual hypotheses, with quadratic covariation $[X](t)=\int_0^tA(s)\,ds$ for a cadlag adapted $S_d^+$-valued process $A$. Let $F^1,F^2\in\mathbb C_b^{1,2}([0,T))$ be nonanticipative functionals verifying (10), and suppose that
--   $$\forall t\in[0,T),\qquad F^1_t(X_t,A_t)=F^2_t(X_t,A_t)\quad\mathbb P\text{-a.s.}\tag{38}$$
--   Then, outside an evanescent set, for every $t\in(0,T)$,
--   $$\big[\nabla_xF^1_t(X_t,A_t)-\nabla_xF^2_t(X_t,A_t)\big]^{\top}A(t-)\big[\nabla_xF^1_t(X_t,A_t)-\nabla_xF^2_t(X_t,A_t)\big]=0.\tag{39}$$
--
--   When $A(t-)$ is nonsingular, this says that the process $\nabla_xF_t(X_t,A_t)$ depends only on the process $F_t(X_t,A_t)$ and not on the functional representing it, which is what makes the vertical derivative $\nabla_XY$ of a process (Definition 4.5) well defined.
--
--   **Formalization Note.** "Outside an evanescent set" is: for $\mathbb P$-almost every $\omega$, for all $t$. The statement is made for $0<t<T$; the page says $t\in[0,T)$. At $t=0$ the claim fails: for $X=W$ a Brownian motion started at $0$, $A=1$, $F^1=0$ and $F^2_t(x,v)=c\,x(0)\,k(t)$ with $k$ smooth and $k(0)=1$, both functionals are in $\mathbb C_b^{1,2}$ and satisfy (38), but $\nabla_xF^2_0=c$ while $\nabla_xF^2_t=0$ for $t>0$. The paper's proof determines the integrand of (41) only on $(0,T)$ (by left-continuity). $A(t-)$ is the left limit of the path of $A$.
-- source:
--   Cont and Fournié, Functional Itô calculus and stochastic integral representation of martingales, arXiv:1002.2446v5, p. 14, Corollary 4.4, (38), (39)

import Mathlib
import Definitions.Def_auto_M05_f3f59_EthierKurtz_HasCrossVariation
import Definitions.Def_FunctionalIto_Representation_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators Matrix

namespace FunctionalIto.Representation

theorem corollary_4_4 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (X V M : ℝ≥0 → Ω → (Fin d → ℝ)) (A : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ)
    (hS : IsContSemimartingaleSetting P ℱ X V M A) (T : ℝ≥0)
    (F₁ DF₁ : Functional d ℝ) (gradF₁ : Functional d (Fin d → ℝ))
    (hessF₁ : Functional d (Matrix (Fin d) (Fin d) ℝ))
    (hF₁ : IsC12b T F₁ DF₁ gradF₁ hessF₁) (h10₁ : PredictableInV T F₁)
    (F₂ DF₂ : Functional d ℝ) (gradF₂ : Functional d (Fin d → ℝ))
    (hessF₂ : Functional d (Matrix (Fin d) (Fin d) ℝ))
    (hF₂ : IsC12b T F₂ DF₂ gradF₂ hessF₂) (h10₂ : PredictableInV T F₂)
    (h38 : ∀ t < T, ∀ᵐ ω ∂P,
      F₁ t (fun s => X s ω) (fun s => A s ω) = F₂ t (fun s => X s ω) (fun s => A s ω)) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < T →
      (gradF₁ t (fun s => X s ω) (fun s => A s ω) - gradF₂ t (fun s => X s ω) (fun s => A s ω)) ⬝ᵥ
        (Function.leftLim (fun s => A s ω) t *ᵥ
          (gradF₁ t (fun s => X s ω) (fun s => A s ω) -
            gradF₂ t (fun s => X s ω) (fun s => A s ω))) = 0 := by sorry

end FunctionalIto.Representation
