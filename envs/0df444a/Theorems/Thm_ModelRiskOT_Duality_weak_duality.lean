-- Prove2me | Theorems.Thm_ModelRiskOT_Duality_weak_duality
-- name    : ModelRiskOT.Duality.weak_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T17:38:52.885989+00:00
-- url     : https://prove2.me/theorems/711e452c-474b-4cc7-a459-6258b95b4183
-- title:
--   (5) — weak duality: $I(\pi)\le J(\lambda,\varphi)$, hence $I\le J$
-- statement:
--   Let $S$ be a Polish space, $\mu$ a Borel probability measure on $S$, $c : S\times S\to[0,\infty)$ a lower semicontinuous cost with $c(x,y)=0$ if and only if $x=y$ (Assumption (A1)), $f : S\to\mathbb R$ upper semicontinuous and $\mu$-integrable (Assumption (A2)), and $\delta>0$. Then for every $\pi\in\Phi_{\mu,\delta}$ and every $(\lambda,\varphi)\in\Lambda_{c,f}$,
--
--   $$I(\pi)=\int f(y)\,d\pi(x,y)\;\le\;\lambda\delta+\int\varphi\,d\mu=J(\lambda,\varphi),$$
--
--   and consequently $I=\sup_{\pi\in\Phi_{\mu,\delta}}I(\pi)\le\inf_{(\lambda,\varphi)\in\Lambda_{c,f}}J(\lambda,\varphi)=J$.
--
--   Weak duality is the easy half of Theorem 1(a) and the inequality used in the proofs of Propositions 5 and 6.
--
--   **Formalization Note** The space $S$ is a Polish space with its Borel σ-algebra; the cost $c$ is real-valued and written curried, $c\,x\,y = c(x,y)$; (A1) is the structure `AssumptionA1`; (A2) is the pair of hypotheses `UpperSemicontinuous f` and `Integrable f μ`. Values that can be infinite ($I$, $J$, $I(\pi)$, $J(\lambda,\varphi)$, $\varphi_\lambda$) live in `EReal`; an integral of an extended-real function is $\int\varphi^+ - \int\varphi^-$ with lower Lebesgue integrals, and $\infty-\infty$ evaluates to $-\infty$, so a coupling with $\int f^-\,d\pi=\infty$ never raises the primal supremum (the paper's footnote 2 reading).
-- source:
--   Blanchet & Murthy, Quantifying Distributional Model Risk via Optimal Transport, arXiv:1604.01446v2, p. 6, §2.2.1, Eq. (5)

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_AssumptionA1
import Definitions.Def_ModelRiskOT_Duality_primalValue
import Definitions.Def_ModelRiskOT_Duality_dualValue

open MeasureTheory

namespace ModelRiskOT.Duality

/-- **Weak duality (5)** (Blanchet & Murthy, arXiv:1604.01446v2, §2.2.1, p. 6). Under (A1) and
(A2), with `δ > 0`: `I(π) ≤ J(λ, φ)` for every `π ∈ Φ_{μ,δ}` and `(λ, φ) ∈ Λ_{c,f}`; hence
`I ≤ J`. -/
theorem weak_duality {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S] [BorelSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (c : S → S → ℝ) (hc : AssumptionA1 c)
    (f : S → ℝ) (hf_usc : UpperSemicontinuous f) (hf_int : Integrable f μ)
    (δ : ℝ) (hδ : 0 < δ) :
    (∀ π ∈ primalFeasible c μ δ, ∀ p ∈ dualFeasible c f Set.univ,
        primalObj f π ≤ dualObj μ δ p.1 p.2) ∧
      primalValue c f μ δ ≤ dualValue c f μ δ := by sorry

end ModelRiskOT.Duality
