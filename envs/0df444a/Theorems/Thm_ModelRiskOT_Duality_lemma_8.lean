-- Prove2me | Theorems.Thm_ModelRiskOT_Duality_lemma_8
-- name    : ModelRiskOT.Duality.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T17:16:15.916765+00:00
-- url     : https://prove2.me/theorems/0064b655-276b-4787-82ce-641d0c84a9c4
-- title:
--   Lemma 8 — $\sup_{\pi\in E}\int\sup_{y\in S_\pi}\{f(y)-\lambda c(x,y)\}d\mu=\int\varphi_\lambda\,d\mu$
-- statement:
--   Let $S$ be a Polish space, $\mu$ a Borel probability measure on $S$, $c$ a cost satisfying (A1) and $f:S\to\mathbb R$ upper semicontinuous and $\mu$-integrable (A2). Let $E$ be the set of probability measures on $S\times S$ satisfying conditions (a)–(c) of Proposition 7, and $S_\pi=\mathrm{Spt}(\pi_X)\cup\mathrm{Spt}(\pi_Y)$. Then for every $\lambda\ge0$,
--
--   $$\sup_{\pi\in E}\int\sup_{y\in S_\pi}\{f(y)-\lambda c(x,y)\}\,d\mu(x)=\int\sup_{y\in S}\{f(y)-\lambda c(x,y)\}\,d\mu(x).$$
--
--   Lemma 8 is the last step of the proof of Theorem 1(a): it removes the restriction $y\in S_\pi$ after the minimax exchange.
--
--   **Formalization Note** The space $S$ is a Polish space with its Borel σ-algebra; the cost $c$ is real-valued and written curried, $c\,x\,y = c(x,y)$; (A1) is the structure `AssumptionA1`; (A2) is the pair of hypotheses `UpperSemicontinuous f` and `Integrable f μ`. Values that can be infinite ($I$, $J$, $I(\pi)$, $J(\lambda,\varphi)$, $\varphi_\lambda$) live in `EReal`; an integral of an extended-real function is $\int\varphi^+ - \int\varphi^-$ with lower Lebesgue integrals, and $\infty-\infty$ evaluates to $-\infty$, so a coupling with $\int f^-\,d\pi=\infty$ never raises the primal supremum (the paper's footnote 2 reading).
-- source:
--   Blanchet & Murthy, Quantifying Distributional Model Risk via Optimal Transport, arXiv:1604.01446v2, p. 23, §4.3, Lemma 8 (E defined on p. 22)

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_AssumptionA1
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ModelRiskOT_Duality_phiLam
import Definitions.Def_ModelRiskOT_Duality_admissibleSet

open MeasureTheory

namespace ModelRiskOT.Duality

/-- **Lemma 8** (Blanchet & Murthy, arXiv:1604.01446v2, §4.3, p. 23). Under (A1) and (A2), for
every `λ ≥ 0`,
`sup_{π ∈ E} ∫ sup_{y ∈ S_π} {f(y) − λ c(x, y)} dμ(x) = ∫ sup_{y ∈ S} {f(y) − λ c(x, y)} dμ(x)`,
where `E` is the set of probability measures on `S × S` satisfying conditions (a)–(c) of
Proposition 7 (`admissibleSet`) and `S_π = Spt(π_X) ∪ Spt(π_Y)` (`supportUnion`). -/
theorem lemma_8 {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S] [BorelSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (c : S → S → ℝ) (hc : AssumptionA1 c)
    (f : S → ℝ) (hf_usc : UpperSemicontinuous f) (hf_int : Integrable f μ)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    (⨆ π ∈ admissibleSet c f μ, extIntegral μ (phiLamOn c f lam (supportUnion π))) =
      extIntegral μ (phiLam c f lam) := by sorry

end ModelRiskOT.Duality
