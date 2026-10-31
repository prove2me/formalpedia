-- Prove2me | Theorems.Thm_KallMayerSLP_RecourseBounds_example_2_1
-- name    : KallMayerSLP.RecourseBounds.example_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:12:11.09867+00:00
-- url     : https://prove2.me/theorems/196c17f5-b1ae-4a3c-9cba-8a395fa73176
-- title:
--   Example 2.1 — the product E–M bound fails for dependent components
-- statement:
--   Let $\xi\in\mathbb R^2$ take the values $(0,0),(1,0),(0,1),(1,1)$ with probabilities $0.1,0.2,0.1,0.6$. Then:
--
--   1. $\mathbb E[\xi]=(0.8,0.7)$; the marginals are $\mathbb P(\xi_1=0)=0.2$, $\mathbb P(\xi_1=1)=0.8$, $\mathbb P(\xi_2=0)=0.3$, $\mathbb P(\xi_2=1)=0.7$;
--   2. the components of $\xi$ are not independent;
--   3. the product E–M distribution of Theorem 2.5 on the vertices of $\Xi=[0,1]^2$ is $0.06,0.24,0.14,0.56$ on $(0,0),(1,0),(0,1),(1,1)$, with mean $(0.8,0.7)$;
--   4. for every $\varphi$ with $\varphi(0,0)=\varphi(1,0)=\varphi(0,1)=0$ and $\varphi(1,1)=1$,
--   $$
--   \mathbb E_\xi[\varphi(\xi)]=0.6,\qquad \mathbb E_\eta[\varphi(\eta)]=0.56;
--   $$
--   5. hence the E–M inequality (2.21) $\mathbb E_\xi[\varphi(\xi)]\le\mathbb E_\eta[\varphi(\eta)]$ fails for some convex $\varphi$ on $[0,1]^2$.
--
--   This is why the independent-case bound must be replaced by the generalized E–M distribution of Lemma 2.7 when components are dependent.
--
--   **Formalization Note** The law is a sum of four Dirac masses on `Fin 2 → ℝ`; vertices are Boolean vectors with `true ↦ 1`. The product E–M weights and bound are the platform's `emVertexWeight 0 1 ξ̄` and `emUpperBound 0 1 ξ̄`.
--
--   Differences from the source:
--   - generalization: for any convex φ(·,·) with the four values, IE_ξ[φ(ξ)] = 0.6 and IE_η[φ(η)] = 0.56 → for any function φ with the four values; reason: both expectations only see the four values; the convex case is included
--   - encoding: the E–M inequality (2.21) does not hold → ¬ ∀ φ convex on [0,1]², ∫ φ dP ≤ emUpperBound 0 1 ξ̄ φ; reason: (2.21) is a statement about every convex φ on Ξ
--   - encoding: ξ with the given realizations and probabilities → P = Σ ofReal(pⱼ) • dirac(xⱼ) on Fin 2 → ℝ; reason: the law of ξ
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, Example 2.1, p.215 (PDF 224)

import Mathlib
import Definitions.Def_NumStochOpt_Bounds_EdmundsonMadansky

open MeasureTheory

namespace KallMayerSLP.RecourseBounds

/-- **Chapter 3, Example 2.1 — the product E–M bound fails for dependent components.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, Example 2.1, printed p.215
(PDF 224): `ξ ∈ ℝ²` takes the values `(0,0), (1,0), (0,1), (1,1)` with probabilities
`0.1, 0.2, 0.1, 0.6`; its expectation is `ξ̄ = (0.8, 0.7)`, the marginals are
`IP_{ξ₁}(0) = 0.2, IP_{ξ₁}(1) = 0.8`, `IP_{ξ₂}(0) = 0.3, IP_{ξ₂}(1) = 0.7`, "being obviously
stochastically dependent"; the E–M distribution of Th. 2.5 puts `0.06, 0.24, 0.14, 0.56` on the four
vertices, "and the expectation `η̄ = (0.8, 0.7)`"; "for any convex function `φ(·,·)` such that `φ(0,0) = φ(1,0) = φ(0,1) = 0` and
`φ(1,1) = 1` we get `IE_ξ[φ(ξ)] = 0.6` and `IE_η[φ(η)] = 0.56`. Hence, in this case, with the E–M
distribution (2.20) as derived for the independent case, the E–M inequality (2.21) does not hold."

**Formalization Note.** Points of `ℝ²` are `Fin 2 → ℝ` (`![a, b]`), the box is `Ξ = [0,1]²`
(`α = 0`, `β = 1`); a vertex is a Boolean vector (`true ↦ 1`, `false ↦ 0`) and
`NumStochOpt.Bounds.emVertexWeight 0 1 ξ̄ v` is its E–M probability (2.19)–(2.20);
`NumStochOpt.Bounds.emUpperBound 0 1 ξ̄ φ` is `IE_η[φ(η)]`. The two values `0.6`, `0.56` are stated
for every function with the four prescribed values (the book says "convex"; convexity is not used by
these two values). The last clause is the failure of (2.21): not every convex function on `Ξ`
satisfies `IE_ξ[φ(ξ)] ≤ IE_η[φ(η)]`. -/
theorem example_2_1 (P : Measure (Fin 2 → ℝ))
    (hP : P = ENNReal.ofReal 0.1 • Measure.dirac ![0, 0] + ENNReal.ofReal 0.2 • Measure.dirac ![1, 0] +
      ENNReal.ofReal 0.1 • Measure.dirac ![0, 1] + ENNReal.ofReal 0.6 • Measure.dirac ![1, 1]) :
    IsProbabilityMeasure P ∧
    ∫ x, x ∂P = ![0.8, 0.7] ∧
    P.real {x | x 0 = 0} = 0.2 ∧ P.real {x | x 0 = 1} = 0.8 ∧
    P.real {x | x 1 = 0} = 0.3 ∧ P.real {x | x 1 = 1} = 0.7 ∧
    ¬ ProbabilityTheory.iIndepFun (fun i (x : Fin 2 → ℝ) => x i) P ∧
    NumStochOpt.Bounds.emVertexWeight 0 1 ![0.8, 0.7] ![false, false] = 0.06 ∧
    NumStochOpt.Bounds.emVertexWeight 0 1 ![0.8, 0.7] ![true, false] = 0.24 ∧
    NumStochOpt.Bounds.emVertexWeight 0 1 ![0.8, 0.7] ![false, true] = 0.14 ∧
    NumStochOpt.Bounds.emVertexWeight 0 1 ![0.8, 0.7] ![true, true] = 0.56 ∧
    ∑ v : Fin 2 → Bool, NumStochOpt.Bounds.emVertexWeight 0 1 ![0.8, 0.7] v •
      NumStochOpt.Bounds.boxVertex 0 1 v = ![0.8, 0.7] ∧
    (∀ φ : (Fin 2 → ℝ) → ℝ, φ ![0, 0] = 0 → φ ![1, 0] = 0 → φ ![0, 1] = 0 → φ ![1, 1] = 1 →
      ∫ x, φ x ∂P = 0.6 ∧ NumStochOpt.Bounds.emUpperBound 0 1 ![0.8, 0.7] φ = 0.56) ∧
    ¬ (∀ φ : (Fin 2 → ℝ) → ℝ, ConvexOn ℝ (Set.Icc 0 1) φ →
      ∫ x, φ x ∂P ≤ NumStochOpt.Bounds.emUpperBound 0 1 (fun i => ∫ x, x i ∂P) φ) := by sorry

end KallMayerSLP.RecourseBounds
