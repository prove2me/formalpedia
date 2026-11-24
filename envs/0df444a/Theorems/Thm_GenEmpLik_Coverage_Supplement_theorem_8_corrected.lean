-- Prove2me | Theorems.Thm_GenEmpLik_Coverage_Supplement_theorem_8_corrected
-- name    : GenEmpLik.Coverage.Supplement.theorem_8_corrected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T23:16:28.116302+00:00
-- url     : https://prove2.me/theorems/0633ab8e-cbff-4f86-b35b-818b2425cab0
-- title:
--   Theorem 8 (corrected: dependent extension needs the loss strong law) — convex consistency
-- statement:
--   Let $X\subset\mathbb R^d$ be nonempty and closed. Let $P_0$ be the common marginal law of measurable observations $\xi_i$, which may be dependent. Assume Assumptions A, C and D. Thus the sample losses are proper closed convex functions on the convex set $X$, and either $X$ is compact or the population risk $F(x)=E_{P_0}\ell(x;\xi)$ is coercive. For one $\epsilon>0$, require $E_{P_0}|\ell(x;\xi)|^{1+\epsilon}<\infty$ for every $x\in X$. Also require an integrable local lower bound: for every $x\in X$ some neighborhood $U_x$ has $g(x;z)\le\ell(y;z)$ for all $y\in U_x\cap X$, with $E_{P_0}|g(x;\xi)|<\infty$.
--
--   Assume the pointwise almost-sure strong laws for both $\ell(x;\xi)$ and $|\ell(x;\xi)|^{1+\epsilon}$, at every $x\in X$. Both hold under the source's default iid sampling. Fix $\rho\ge0$, write $\widehat F_n$ for the empirical robust risk and let $\widehat S_n=\arg\min_X\widehat F_n$ and $S_0=\arg\min_XF$. Then
--   $$\inf_{x\in X}\widehat F_n(x)\longrightarrow\inf_{x\in X}F(x),\qquad d_\subset(\widehat S_n,S_0)\longrightarrow0\quad\text{in outer probability}.$$
--   This retains both conclusions on possibly unbounded decision regions, with pointwise moments rather than a common envelope.
--
--   **Formalization Note** The value infimum is extended-real so an early unbounded-below sample is not replaced by zero. The directed solution distance is the published $[0,\infty]$-valued distance. The extra loss strong law makes explicit the use of the ordinary strong law in Appendix E.2, p. 48. The displayed moment law alone does not justify the prose's dependent extension: perfectly dependent Rademacher losses have constant absolute moments but inconsistent means. No iid case is excluded; arbitrary common-marginal samples satisfying both laws are retained.
--
--   Differences from the source:
--   - correction: the dependent extension following Theorem 8 invokes only the absolute-moment strong law → both the loss and absolute-moment pointwise strong laws are explicit; reason: the last term of the bound on p. 48 needs the loss law; a perfectly dependent Rademacher sequence refutes the extension without it (DISPROOF.md)
--   - generalization: iid sampling by the convention on p. 5, with a dependent extension discussed on p. 17 → any common-marginal sample satisfying both pointwise laws; reason: these are the exact convergence inputs used in Appendix E.2 and include every iid instance
--   - encoding: infimum of the robust risk and directed solution distance → an EReal infimum and the published ENNReal directed distance; reason: these retain infinite early-sample values and avoid a junk real infimum; the population optimum is finite by the stated assumptions
--   - generalization: the observation space in the optimization setup is separable metric → an arbitrary measurable observation space; reason: these results only use measurable losses and sample laws, while the decision space remains finite dimensional
--   - encoding: nonempty closed X and measurable random losses → explicit domain, loss-measurability and common-marginal binders; reason: the domain is fixed in (1), p. 1; all integrals are genuine under the pointwise moments
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 17, Theorem 8; proof p. 48

import Mathlib
import Definitions.Def_GenEmpLik_Coverage_AssumptionA
import Definitions.Def_GenEmpLik_Coverage_optimalValue
import Definitions.Def_GenEmpLik_Coverage_Supplement_AssumptionC
import Definitions.Def_GenEmpLik_Coverage_Supplement_AssumptionD
import Definitions.Def_GenEmpLik_Coverage_Supplement_robustProblem
import Definitions.Def_VarianceRegularization_Expansion_empMean

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

namespace GenEmpLik.Coverage.Supplement

/-- Theorem 8, p. 17, with the loss strong law used on p. 48 made explicit for
its dependent-data extension. Both laws hold for every iid sample by the SLLN.
No common envelope or bounded decision domain is assumed. Extended-real value
convergence does not silently replace an unbounded early infimum by zero. -/
theorem theorem_8_corrected
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Ξ) (d : ℕ)
    (X : Set (EuclideanSpace ℝ (Fin d)))
    (ℓ : EuclideanSpace ℝ (Fin d) → Ξ → ℝ)
    (f : ℝ → EReal) (ρ ε : ℝ) (hρ : 0 ≤ ρ) (hε : 0 < ε)
    (hA : GenEmpLik.Coverage.AssumptionA f)
    (hX : X.Nonempty) (hclosed : IsClosed X)
    (hC : AssumptionC X ℓ (μ.map (ξ 0)))
    (hD : AssumptionD X ℓ (μ.map (ξ 0)))
    (hℓmeas : ∀ x ∈ X, Measurable (ℓ x))
    (hmoment : ∀ x ∈ X,
      Integrable (fun z => |ℓ x z| ^ (1 + ε)) (μ.map (ξ 0)))
    (g : EuclideanSpace ℝ (Fin d) → Ξ → ℝ)
    (hglower : ∀ x ∈ X, ∃ U ∈ 𝓝 x,
      ∀ z, ∀ y ∈ U ∩ X, g x z ≤ ℓ y z)
    (hgint : ∀ x ∈ X, Integrable (g x) (μ.map (ξ 0)))
    (hξmeas : ∀ i, Measurable (ξ i))
    (hξident : ∀ i, IdentDistrib (ξ i) (ξ 0) μ μ)
    (hlosslaw : ∀ x ∈ X, ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => VarianceRegularization.Expansion.empMean
        (fun i : Fin n => ℓ x (ξ i ω))) atTop (𝓝 (∫ z, ℓ x z ∂(μ.map (ξ 0)))))
    (hmomentlaw : ∀ x ∈ X, ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => VarianceRegularization.Expansion.empMean
        (fun i : Fin n => |ℓ x (ξ i ω)| ^ (1 + ε))) atTop
        (𝓝 (∫ z, |ℓ x z| ^ (1 + ε) ∂(μ.map (ξ 0))))) :
    (∀ δ : ℝ, 0 < δ → Tendsto (fun n : ℕ => μ {ω |
      robustValue X ℓ f ρ (fun i : Fin n => ξ i ω) <
        ((GenEmpLik.Coverage.optimalValue X ℓ (μ.map (ξ 0)) - δ : ℝ) : EReal) ∨
      ((GenEmpLik.Coverage.optimalValue X ℓ (μ.map (ξ 0)) + δ : ℝ) : EReal) <
        robustValue X ℓ f ρ (fun i : Fin n => ξ i ω)}) atTop (𝓝 0)) ∧
    (∀ δ : ℝ, 0 < δ → Tendsto (fun n : ℕ => μ {ω |
      ENNReal.ofReal δ < GenEmpLik.Consistency.inclDist
        (robustSolutions X ℓ f ρ (fun i : Fin n => ξ i ω))
        (GenEmpLik.Consistency.argminSet X
          (fun x => ∫ z, ℓ x z ∂(μ.map (ξ 0))))}) atTop (𝓝 0)) := by sorry

end GenEmpLik.Coverage.Supplement
