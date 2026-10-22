-- Prove2me | Theorems.Thm_InterpOptStop_SAA_theorem_1
-- name    : InterpOptStop.SAA.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:51.077164+00:00
-- url     : https://prove2.me/theorems/5f9176d1-20de-4481-abd1-1697a16dafff
-- title:
--   Theorem 1, p. 10 — a.s. ∃Ω0 ∀Ω ≥ Ω0 ∀π ∈ Πtree(d): |J^π(x̄) − Ĵ^π(x̄)| ≤ ϵ
-- statement:
--   Consider the stopping problem under Assumptions 1, 2 and 3 (bounded state space, rewards in $[0,G]$, and probabilities of sets controlled by their Lebesgue measure through $f$), with an i.i.d. sample of trajectories from the law of the process started at $\bar{\mathbf x}$. Fix a finite tree depth $d$ and $\epsilon>0$. With probability one there is a finite sample size $\Omega_0$ such that for all $\Omega\ge\Omega_0$ and all tree policies $\pi\in\Pi_{\mathrm{tree}}(d)$,
--   $$\big|J^\pi(\bar{\mathbf x})-\hat J^\pi(\bar{\mathbf x})\big|\le\epsilon.$$
--
--   The sample-average value therefore converges to the true value **uniformly** over all tree policies of depth at most $d$, including all real split points. Corollary 1 is a consequence. Section EC.1.2 of the paper shows that the statement fails without the depth bound.
--
--   **Formalization Note** The quantifier order is the content: one almost-sure event, then one $\Omega_0$, valid for every skeleton of depth $\le d$ and every split-point vector. The model and the disclosed readings are as in Lemma EC.1: i.i.d. samples, $\beta\in[0,1]$, measurable $g$, and Assumption 3 over measurable sets of finite Lebesgue measure without the printed codomain $[0,1]$ of $f$, which as printed is unsatisfiable for $n\ge1$, $T\ge2$.
-- source:
--   Ciocan & Mišić, Interpretable Optimal Stopping, arXiv:1812.07211v2, Theorem 1, p. 10

import Mathlib
import Definitions.Def_InterpOptStop_SAA_StoppingModel
import Definitions.Def_InterpOptStop_SAA_TreePolicy
open MeasureTheory ProbabilityTheory Filter Topology

namespace InterpOptStop.SAA

/-- Theorem 1 (arXiv:1812.07211v2, p. 10): almost surely, the sample-average value converges to
the true value uniformly over all tree policies of depth at most `d`. -/
theorem theorem_1 {n T : ℕ}
    (hT : 0 < T)
    (xbar : Fin n → ℝ)
    (X : Set (Fin n → ℝ)) (Xi : Fin n → Set ℝ) (hXprod : X = Set.univ.pi Xi)
    (hXtb : TotallyBounded X) (hXdiam : ∀ x ∈ X, ∀ y ∈ X, ‖x - y‖ ≤ 1)
    (μ : Measure (Fin T → Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hstart : ∀ᵐ x ∂μ, x ⟨0, hT⟩ = xbar)
    (hinX : ∀ᵐ x ∂μ, ∀ k, x k ∈ X)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (g : Fin T → (Fin n → ℝ) → ℝ) (hgm : ∀ k, Measurable (g k))
    (G : ℝ) (hg : ∀ k, ∀ x ∈ X, 0 ≤ g k x ∧ g k x ≤ G)
    (f : ℝ → ℝ) (hf0 : f 0 = 0) (hfmono : StrictMonoOn f (Set.Ici 0))
    (hfcont : ContinuousOn f (Set.Ici 0))
    (hA3 : ∀ A : Set (Fin n → ℝ), MeasurableSet A → volume A ≠ ⊤ →
      ∀ k : Fin T, (k : ℕ) ≠ 0 → (μ {x | x k ∈ A}).toReal ≤ f (volume A).toReal)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Fin T → Fin n → ℝ) (hξm : ∀ k, Measurable (ξ k)) (hind : iIndepFun ξ P)
    (hlaw : ∀ k, P.map (ξ k) = μ) :
    ∀ (d : ℕ) (ε : ℝ), 0 < ε → ∀ᵐ ω ∂P, ∃ Ω₀ : ℕ, ∀ m ≥ Ω₀, ∀ S : Tree n, S.depth ≤ d →
      ∀ θ : Thresholds,
        |J μ β g (policy S θ) - Jhat (fun k => ξ k ω) m β g (policy S θ)| ≤ ε := by sorry

end InterpOptStop.SAA
