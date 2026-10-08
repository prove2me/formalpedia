-- Prove2me | Theorems.Thm_FunctionalIto_Representation_theorem_5_8
-- name    : FunctionalIto.Representation.theorem_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:18.221993+00:00
-- url     : https://prove2.me/theorems/93c90f9f-2bfa-4bcf-9713-500fc3213440
-- title:
--   Theorem 5.8, pp. 18–19 — ∇_X is closable and extends to a bijective isometry 𝒲^{1,2}(X) → 𝓛²(X) inverting the Itô integral, characterized by (53); with (56)
-- statement:
--   Work under Assumption 5.1: $X(t)=X(0)+\int_0^t\sigma\cdot dW$ with $W$ a standard $d$-dimensional Brownian motion, $\sigma$ an $\mathcal F^W$-progressive matrix process with $\det\sigma\neq0$ $dt\times d\mathbb P$-a.e. and $E\int_0^T\|\sigma\|^2dt<\infty$, working filtration $\mathcal F=\mathcal F^X$, and $[X]=\int A\,dt$ with $A$ cadlag. Let $\mathcal L^2(X)$, $\mathcal I^2(X)$, $D(X)$ and $\mathcal W^{1,2}(X)$ be as in the definitions file. Then the vertical derivative $\nabla_X:D(X)\to\mathcal L^2(X)$ is closable on $\mathcal W^{1,2}(X)$, and its closure defines a bijective isometry
--   $$\nabla_X:\mathcal W^{1,2}(X)\to\mathcal L^2(X),\qquad\int_0^\cdot\varphi\cdot dX\mapsto\varphi,\tag{52}$$
--   characterized by the integration by parts formula: for $Y\in\mathcal W^{1,2}(X)$, $\nabla_XY$ is the unique element of $\mathcal L^2(X)$ such that
--   $$\forall Z\in D(X),\qquad E[Y(T)Z(T)]=E\left[\int_0^T\nabla_XY(t)\,\nabla_XZ(t)\,d[X](t)\right].\tag{53}$$
--   In particular
--   $$\forall\varphi\in\mathcal L^2(X),\qquad\nabla_X\Big(\int_0^\cdot\varphi\,dX\Big)=\varphi\tag{56}$$
--   in $\mathcal L^2(X)$.
--
--   Precisely, the statement asserts:
--   1. *closability*: if $Y_n\in D(X)$ with derivatives $\psi_n$, $Y_n\to0$ in $\mathcal I^2(X)$ and $\psi_n\to g$ in $\mathcal L^2(X)$, then $g=0$ in $\mathcal L^2(X)$;
--   2. *existence and surjectivity*: every $Y\in\mathcal W^{1,2}(X)$ has a closure derivative, and every $\varphi\in\mathcal L^2(X)$ is the closure derivative of some $Y$;
--   3. *isometry*: if $\varphi,\varphi'$ are closure derivatives of $Y,Y'$, then $E[(Y(T)-Y'(T))^2]=\|\varphi-\varphi'\|^2_{\mathcal L^2(X)}$;
--   4. *characterization*: a closure derivative $\varphi$ of $Y$ satisfies (53) against every $Z\in D(X)$ (with integrability), and any $\psi\in\mathcal L^2(X)$ satisfying (53) equals $\varphi$ in $\mathcal L^2(X)$;
--   5. *inverse of the Itô integral* (52), (56): if $I=\int_0^\cdot\varphi\cdot dX$ with $\varphi\in\mathcal L^2(X)$, then $\varphi$ is a closure derivative of $I$.
--
--   Combined with $\mathcal W^{1,2}(X)=\mathcal I^2(X)$ (Lemma 5.7), this identifies $\nabla_X$ as the inverse of the Itô integral on all square-integrable martingales of $\mathcal F^X$, which gives the general martingale representation formula of the paper.
--
--   **Formalization Note.** The closure is a relation (the closure of the graph of $\nabla_X$), not a function chosen by `Classical.choose`; existence and uniqueness up to $\mathcal L^2(X)$-null sets are part of the theorem. Uniqueness is stated $d[X]\times d\mathbb P$-a.e., not pointwise. Norms are lower integrals in $[0,\infty]$; the integrals in (53) are real integrals whose integrability is part of the conclusion. The adjoint property (55) is the separate item `theorem_5_8_adjoint`. Two hypotheses the page uses without printing them are included: $\mathcal F=\mathcal F^X$ and $E[X](T)<\infty$.
-- source:
--   Cont and Fournié, Functional Itô calculus and stochastic integral representation of martingales, arXiv:1002.2446v5, pp. 18–19, Theorem 5.8, (52), (53); p. 19, (56)

import Mathlib
import Definitions.Def_auto_M05_f3f59_EthierKurtz_HasCrossVariation
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_FunctionalIto_Representation_Setting
import Definitions.Def_FunctionalIto_Representation_L2

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators Matrix

namespace FunctionalIto.Representation

theorem theorem_5_8
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℝ≥0) (W : ℝ≥0 → Ω → EthierKurtz.SDEState d) (𝒢 ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (σ : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ) (X : ℝ≥0 → Ω → (Fin d → ℝ))
    (A : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ) (hS : IsBrownianSetting P T W 𝒢 σ X ℱ A) :
    -- closability of `∇_X : D(X) → 𝓛²(X)` on `𝒲^{1,2}(X)`
    (∀ (Yn : ℕ → ℝ≥0 → Ω → ℝ) (ψn : ℕ → ℝ≥0 → Ω → (Fin d → ℝ)) (g : ℝ≥0 → Ω → (Fin d → ℝ)),
      (∀ n, IsVertDerivD P ℱ T X A (Yn n) (ψn n)) →
      Tendsto (fun n => I2DistSq P T (Yn n) 0) atTop (𝓝 0) → MemL2X P ℱ T A g →
      Tendsto (fun n => L2XNormSq P T A (ψn n - g)) atTop (𝓝 0) → L2XNormSq P T A g = 0) ∧
    -- the closure is defined on all of `𝒲^{1,2}(X)` and onto `𝓛²(X)`
    (∀ Y, MemW12 P ℱ T X A Y → ∃ φ, IsClosureDeriv P ℱ T X A Y φ) ∧
    (∀ φ, MemL2X P ℱ T A φ → ∃ Y, IsClosureDeriv P ℱ T X A Y φ) ∧
    -- isometry (52)
    (∀ Y Y' φ φ', IsClosureDeriv P ℱ T X A Y φ → IsClosureDeriv P ℱ T X A Y' φ' →
      I2DistSq P T Y Y' = L2XNormSq P T A (φ - φ')) ∧
    -- characterization by the integration by parts formula (53)
    (∀ Y φ, IsClosureDeriv P ℱ T X A Y φ →
      (∀ Z ζ, IsVertDerivD P ℱ T X A Z ζ →
        Integrable (fun ω => Y T ω * Z T ω) P ∧ QIntegrable P T A φ ζ ∧
          ∫ ω, Y T ω * Z T ω ∂P = QInner P T A φ ζ) ∧
      (∀ ψ, MemL2X P ℱ T A ψ →
        (∀ Z ζ, IsVertDerivD P ℱ T X A Z ζ → ∫ ω, Y T ω * Z T ω ∂P = QInner P T A ψ ζ) →
        L2XNormSq P T A (ψ - φ) = 0)) ∧
    -- (52), (56): `∇_X (∫_0^· φ · dX) = φ`
    (∀ φ I, IsItoIntegral P ℱ T X A φ I → IsClosureDeriv P ℱ T X A I φ) := by sorry

end FunctionalIto.Representation
