-- Prove2me | Theorems.Thm_ModelRiskOT_Duality_theorem_1
-- name    : ModelRiskOT.Duality.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:39:49.023978+00:00
-- url     : https://prove2.me/theorems/2e87ad98-3647-4cfd-abe0-205491a24ae7
-- title:
--   Theorem 1 — strong duality $I=J$, a dual optimizer $(\lambda^*,\varphi_{\lambda^*})$ and complementary slackness
-- statement:
--   Let $S$ be a Polish space, $\mu$ a Borel probability measure on $S$, $c : S\times S\to[0,\infty)$ a lower semicontinuous cost with $c(x,y)=0$ if and only if $x=y$ (Assumption (A1)), $f : S\to\mathbb R$ upper semicontinuous and $\mu$-integrable (Assumption (A2)), and $\delta>0$. Let $I=\sup\{\int f(y)\,d\pi(x,y):\pi\in\Phi_{\mu,\delta}\}$ be the worst-case expectation of $f$ over transport plans out of $\mu$ with cost at most $\delta$, and $J=\inf\{\lambda\delta+\int\varphi\,d\mu:(\lambda,\varphi)\in\Lambda_{c,f}\}$ its dual. For $\lambda\ge0$ let $\varphi_\lambda(x)=\sup_{y\in S}\{f(y)-\lambda c(x,y)\}$. Then:
--
--   1. **(a) Strong duality.**
--   $$\sup\{I(\pi):\pi\in\Phi_{\mu,\delta}\}=\inf\{J(\lambda,\varphi):(\lambda,\varphi)\in\Lambda_{c,f}\}.$$
--   2. **(b) Dual attainment.** There is $\lambda\ge0$ such that $(\lambda,\varphi_\lambda)\in\Lambda_{c,f}$ and $J(\lambda,\varphi_\lambda)=J$.
--   3. **(b) Complementary slackness, "if".** For $\pi^*\in\Phi_{\mu,\delta}$ and $(\lambda^*,\varphi_{\lambda^*})\in\Lambda_{c,f}$, if
--   $$f(y)-\lambda^*c(x,y)=\sup_{z\in S}\{f(z)-\lambda^*c(x,z)\}\ \ \pi^*\text{-a.s.}\quad(8a)\qquad\text{and}\qquad \lambda^*\Big(\int c\,d\pi^*-\delta\Big)=0\quad(8b),$$
--   then $\pi^*$ is a primal optimizer ($I(\pi^*)=I$), $(\lambda^*,\varphi_{\lambda^*})$ is a dual optimizer ($J(\lambda^*,\varphi_{\lambda^*})=J$), and $I(\pi^*)=J(\lambda^*,\varphi_{\lambda^*})$.
--   4. **(b) Complementary slackness, "only if".** Conversely, if $\pi^*$ and $(\lambda^*,\varphi_{\lambda^*})$ are as in 3., are primal and dual optimizers with $I(\pi^*)=J(\lambda^*,\varphi_{\lambda^*})$, and $J(\lambda^*,\varphi_{\lambda^*})<\infty$, then (8a) and (8b) hold.
--
--   Theorem 1 says that the worst-case expectation over an optimal-transport ball on a general Polish space, with only lower semicontinuous costs and upper semicontinuous integrable $f$, equals a one-dimensional dual problem over $\lambda$, and it characterizes worst-case transport plans.
--
--   **Formalization Note** The finiteness hypothesis $J(\lambda^*,\varphi_{\lambda^*})<\infty$ in item 4 is implicit in the paper: when $f$ outgrows $c$ on a set of positive $\mu$-measure, $\varphi_{\lambda}\equiv\infty$ there, $I=J=\infty$, and an optimal $\pi^*$ with $I(\pi^*)=\infty$ can exist while (8a) is impossible ($f(y)-\lambda^*c(x,y)$ is finite). The direction "if" holds without it. By weak duality, "primal and dual optimizers satisfying $I(\pi^*)=J(\lambda^*,\varphi_{\lambda^*})$" is equivalent to $I(\pi^*)=J(\lambda^*,\varphi_{\lambda^*})$ alone; the statement spells out all three equalities. In (8b) the cost integral is converted to a real number, which is safe because it is at most $\delta$. The space $S$ is a Polish space with its Borel σ-algebra; the cost $c$ is real-valued and written curried, $c\,x\,y = c(x,y)$; (A1) is the structure `AssumptionA1`; (A2) is the pair of hypotheses `UpperSemicontinuous f` and `Integrable f μ`. Values that can be infinite ($I$, $J$, $I(\pi)$, $J(\lambda,\varphi)$, $\varphi_\lambda$) live in `EReal`; an integral of an extended-real function is $\int\varphi^+ - \int\varphi^-$ with lower Lebesgue integrals, and $\infty-\infty$ evaluates to $-\infty$, so a coupling with $\int f^-\,d\pi=\infty$ never raises the primal supremum (the paper's footnote 2 reading).
-- source:
--   Blanchet & Murthy, Quantifying Distributional Model Risk via Optimal Transport, arXiv:1604.01446v2, p. 7, Theorem 1 (a), (b), Eqs. (8a)–(8b)

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_AssumptionA1
import Definitions.Def_ModelRiskOT_Duality_primalValue
import Definitions.Def_ModelRiskOT_Duality_dualValue
import Definitions.Def_ModelRiskOT_Duality_phiLam

open MeasureTheory

namespace ModelRiskOT.Duality

/-- **Theorem 1** (Blanchet & Murthy, arXiv:1604.01446v2, p. 7). Under (A1) and (A2), with `δ > 0`:

1. (a) strong duality `I = J`;
2. (b) a dual optimizer of the form `(λ, φ_λ)`, `λ ≥ 0`, exists;
3. (b, "if") for `π* ∈ Φ_{μ,δ}` and `(λ*, φ_{λ*}) ∈ Λ_{c,f}`, the complementary slackness
   conditions (8a) `f(y) − λ* c(x, y) = sup_z {f(z) − λ* c(x, z)}` `π*`-a.s. and
   (8b) `λ* (∫ c dπ* − δ) = 0` imply that `π*` and `(λ*, φ_{λ*})` are primal and dual optimizers
   with `I(π*) = J(λ*, φ_{λ*})`;
4. (b, "only if") conversely, if `π*` and `(λ*, φ_{λ*})` are primal and dual optimizers with
   `I(π*) = J(λ*, φ_{λ*})` **and `J(λ*, φ_{λ*}) < ∞`** (a hypothesis the page leaves implicit:
   without it the "only if" fails when `I = J = ∞`), then (8a) and (8b) hold. -/
theorem theorem_1 {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S] [BorelSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (c : S → S → ℝ) (hc : AssumptionA1 c)
    (f : S → ℝ) (hf_usc : UpperSemicontinuous f) (hf_int : Integrable f μ)
    (δ : ℝ) (hδ : 0 < δ) :
    primalValue c f μ δ = dualValue c f μ δ ∧
    (∃ lam : ℝ, 0 ≤ lam ∧ (lam, phiLam c f lam) ∈ dualFeasible c f Set.univ ∧
      dualObj μ δ lam (phiLam c f lam) = dualValue c f μ δ) ∧
    (∀ π ∈ primalFeasible c μ δ, ∀ lam : ℝ, (lam, phiLam c f lam) ∈ dualFeasible c f Set.univ →
      ((∀ᵐ p ∂π, ((f p.2 - lam * c p.1 p.2 : ℝ) : EReal) = phiLam c f lam p.1) ∧
        lam * ((∫⁻ p, ENNReal.ofReal (c p.1 p.2) ∂π).toReal - δ) = 0) →
      (primalObj f π = primalValue c f μ δ ∧
        dualObj μ δ lam (phiLam c f lam) = dualValue c f μ δ ∧
        primalObj f π = dualObj μ δ lam (phiLam c f lam))) ∧
    (∀ π ∈ primalFeasible c μ δ, ∀ lam : ℝ, (lam, phiLam c f lam) ∈ dualFeasible c f Set.univ →
      dualObj μ δ lam (phiLam c f lam) ≠ ⊤ →
      (primalObj f π = primalValue c f μ δ ∧
        dualObj μ δ lam (phiLam c f lam) = dualValue c f μ δ ∧
        primalObj f π = dualObj μ δ lam (phiLam c f lam)) →
      ((∀ᵐ p ∂π, ((f p.2 - lam * c p.1 p.2 : ℝ) : EReal) = phiLam c f lam p.1) ∧
        lam * ((∫⁻ p, ENNReal.ofReal (c p.1 p.2) ∂π).toReal - δ) = 0)) := by sorry

end ModelRiskOT.Duality
