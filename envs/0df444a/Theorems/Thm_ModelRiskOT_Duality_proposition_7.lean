-- Prove2me | Theorems.Thm_ModelRiskOT_Duality_proposition_7
-- name    : ModelRiskOT.Duality.proposition_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T17:39:24.990661+00:00
-- url     : https://prove2.me/theorems/a5acfc30-b8cf-4d98-91e4-c3f3b11dd397
-- title:
--   Proposition 7 — $\inf_{(\lambda,\varphi)\in\Lambda(S_\pi\times S_\pi)}J(\lambda,\varphi)\le I$
-- statement:
--   Let $S$ be a Polish space, $\mu$ a Borel probability measure on $S$, $c : S\times S\to[0,\infty)$ a lower semicontinuous cost with $c(x,y)=0$ if and only if $x=y$ (Assumption (A1)), $f : S\to\mathbb R$ upper semicontinuous and $\mu$-integrable (Assumption (A2)), and $\delta>0$. Let $\pi$ be a probability measure on $S\times S$ such that
--
--   1. (a) $\int c(x,y)\,d\pi(x,y)<\infty$;
--   2. (b) $\int f(y)\,d\pi(x,y)\in(-\infty,\infty)$;
--   3. (c) $\pi(A\times S)=\mu(A)$ for every Borel set $A\subseteq S$.
--
--   Let $S_\pi=\mathrm{Spt}(\pi_X)\cup\mathrm{Spt}(\pi_Y)$ and let $\Lambda(S_\pi\times S_\pi)$ be the set of pairs $(\lambda,\varphi)$ with $\lambda\ge0$, $\varphi$ universally measurable and $\varphi(x)+\lambda c(x,y)\ge f(y)$ for all $x,y\in S_\pi$ (29). Then
--
--   $$\inf_{(\lambda,\varphi)\in\Lambda(S_\pi\times S_\pi)}\Big(\lambda\delta+\int\varphi\,d\mu\Big)\le I.$$
--
--   Note that $\pi$ is not required to satisfy the budget $\int c\,d\pi\le\delta$. Proposition 7 carries the compact duality of Proposition 6 to the $\sigma$-compact set $S_\pi\times S_\pi$.
--
--   **Formalization Note** The space $S$ is a Polish space with its Borel σ-algebra; the cost $c$ is real-valued and written curried, $c\,x\,y = c(x,y)$; (A1) is the structure `AssumptionA1`; (A2) is the pair of hypotheses `UpperSemicontinuous f` and `Integrable f μ`. Values that can be infinite ($I$, $J$, $I(\pi)$, $J(\lambda,\varphi)$, $\varphi_\lambda$) live in `EReal`; an integral of an extended-real function is $\int\varphi^+ - \int\varphi^-$ with lower Lebesgue integrals, and $\infty-\infty$ evaluates to $-\infty$, so a coupling with $\int f^-\,d\pi=\infty$ never raises the primal supremum (the paper's footnote 2 reading).
-- source:
--   Blanchet & Murthy, Quantifying Distributional Model Risk via Optimal Transport, arXiv:1604.01446v2, p. 20, §4.3, Proposition 7 (with (29) and §4.2's S_π)

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_AssumptionA1
import Definitions.Def_ModelRiskOT_Duality_primalValue
import Definitions.Def_ModelRiskOT_Duality_dualValue
import Definitions.Def_ModelRiskOT_Duality_admissibleSet

open MeasureTheory

namespace ModelRiskOT.Duality

/-- **Proposition 7** (Blanchet & Murthy, arXiv:1604.01446v2, §4.3, p. 20). Under (A1) and (A2),
with `δ > 0`: let `π` be a probability measure on `S × S` with (a) `∫ c dπ < ∞`,
(b) `∫ f(y) dπ(x, y) ∈ (−∞, ∞)` and (c) `π(A × S) = μ(A)` for every Borel `A`. Then
`inf_{(λ, φ) ∈ Λ(S_π × S_π)} J(λ, φ) ≤ I`, where `S_π = Spt(π_X) ∪ Spt(π_Y)` and `Λ(K × K)` is
(29). No budget constraint `∫ c dπ ≤ δ` is assumed. -/
theorem proposition_7 {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S] [BorelSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (c : S → S → ℝ) (hc : AssumptionA1 c)
    (f : S → ℝ) (hf_usc : UpperSemicontinuous f) (hf_int : Integrable f μ)
    (δ : ℝ) (hδ : 0 < δ)
    (π : Measure (S × S)) [IsProbabilityMeasure π]
    (ha : ∫⁻ p, ENNReal.ofReal (c p.1 p.2) ∂π < ⊤)
    (hb : Integrable (fun p => f p.2) π)
    (hmarg : ∀ A : Set S, MeasurableSet A → π (A ×ˢ Set.univ) = μ A) :
    (⨅ p ∈ dualFeasible c f (supportUnion π), dualObj μ δ p.1 p.2) ≤ primalValue c f μ δ := by sorry

end ModelRiskOT.Duality
