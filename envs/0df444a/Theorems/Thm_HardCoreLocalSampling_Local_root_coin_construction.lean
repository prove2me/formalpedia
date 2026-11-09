-- Prove2me | Theorems.Thm_HardCoreLocalSampling_Local_root_coin_construction
-- name    : HardCoreLocalSampling.Local.root_coin_construction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:53:53.935205+00:00
-- url     : https://prove2.me/theorems/70221ca9-0a71-4dae-82ba-997904f103a8
-- title:
--   Lemma 13 — Root coin construction
-- statement:
--   The following algorithm returns exactly a Bernoulli random variable of mean $p=P_d(y)$. If $d=0$, return the direct coin of mean $1/(1+\lambda)$. For $d\ge1$, $Q=(1-t)^{-d}-1>0$, and:
--
--   1. With probability $2Q$, select $\alpha\ne0$ with probability $q_\alpha/Q$, $q_\alpha=t^{|\alpha|}$. Generate an independent sign of mean $h_\alpha/q_\alpha$, multiply by independent residual factory outputs with multiplicities $\alpha_i$, obtaining $Y\in\{-1,+1\}$, and return $(1+Y)/2$.
--   2. With the remaining probability $1-2Q$, return a coin of mean $(p_0-Q)/(1-2Q)$.
--
--   The expected number of residual-factory invocations and all other local computation costs are bounded by a model-dependent constant. The statement includes the validity of these probabilities and means, and exhibits a machine program with this law and these costs, in which a residual-factory call is one external sign read.
--
--   Differences from the source:
--   - encoding: an algorithm in the informally described word and bit cost model → a finite program of the Machine language; reason: a concrete instruction set of that model; every such program is an algorithm in the source's model, and restricting address arithmetic to increment, decrement and paid conversion only charges more than the source does
--   - encoding: residual factory outputs inside the root algorithm's cost → each call is a read from an independent external sign source of mean z_i, counted separately; reason: the lemma counts factory invocations and bounds the rest of the work separately; the factory's own cost is Lemma 18's
--   - generalization: the true child messages and the centers of Lemma 9 → any real y within η of any centers in [0,U], on any finite dyadic grid for the program; reason: the proof uses only these properties, and the true messages and Lemma 9's centers have them
-- source:
--   Thomas Chen, STOC 2027 submission #462 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/462.pdf, Lemma 13, eqs. (22)–(23), printed p.10 (PDF p.11)

import Mathlib
import Definitions.Def_HardCoreLocalSampling_Local_Params
import Definitions.Def_HardCoreLocalSampling_Local_Factory

namespace HardCoreLocalSampling.Local

/-- Thomas Chen, STOC 2027 submission #462, Lemma 13, printed p.10 (PDF p.11), eqs. (22)–(23).
First part: the validity of the algorithm's probabilities, and that `rootAlgorithm` returns
`true` with probability exactly `p = P_d(y)`. Second part, the cost clause: a machine program
implements it with fair bits and `ext` calls to the residual signs; it has the same law, and
expected residual calls and expected other work both at most a constant depending only on the
model. -/
theorem root_coin_construction (Delta : ℕ) (lam rho eta : ℚ) (hS : Standing Delta lam)
    (hrho : IsContractionConstant Delta lam rho) (heta : IsEta Delta lam rho eta) :
    let t : ℝ := (tParam Delta eta : ℝ)
    let Q : ℕ → ℝ := fun d => ((1 - t)⁻¹) ^ d - 1
    (∀ (d : ℕ), d ≤ Delta → ∀ (c y : Fin d → ℝ), (∀ i, 0 ≤ c i) →
      (∀ i, c i ≤ Umsg (lam : ℝ)) → (∀ i, |y i - c i| ≤ (eta : ℝ)) →
      ∀ (select : PMF (Fin d → ℕ)) (residual : Fin d → PMF Bool),
        (1 ≤ d → select 0 = 0) →
        (∀ α, mdeg α ≠ 0 → select α = ENNReal.ofReal (t ^ mdeg α / Q d)) →
        (∀ i, residual i true = ENNReal.ofReal ((1 + (y i - c i) / (eta : ℝ)) / 2)) →
        let signMean : (Fin d → ℕ) → ℝ := fun α =>
          rootCoeff (lam : ℝ) (eta : ℝ) c α / t ^ mdeg α
        (1 ≤ d → 0 < Q d ∧ 2 * Q d ≤ 1 ∧ (∀ α, |signMean α| ≤ 1) ∧
          0 ≤ (Pd (lam : ℝ) c - Q d) / (1 - 2 * Q d) ∧
          (Pd (lam : ℝ) c - Q d) / (1 - 2 * Q d) ≤ 1) ∧
        rootAlgorithm (lam : ℝ) (Q d) (Pd (lam : ℝ) c) select signMean residual true =
          ENNReal.ofReal (Pd (lam : ℝ) y)) ∧
    (∀ (k J : ℕ), ∃ (P : Program) (C : NNReal),
      ∀ (d : ℕ), d ≤ Delta → ∀ (j : Fin d → ℕ) (y : Fin d → ℝ), (∀ i, j i ≤ J) →
        let c : Fin d → ℝ := fun i => (j i : ℝ) / 2 ^ k
        (∀ i, c i ≤ Umsg (lam : ℝ)) → (∀ i, |y i - c i| ≤ (eta : ℝ)) →
        let init : Config := { N := regsOf [d], Nm := regsOf (List.ofFn j) }
        let extMean : ℕ → ℝ := fun i =>
          if h : i < d then (1 + (y ⟨i, h⟩ - c ⟨i, h⟩) / (eta : ℝ)) / 2 else 0
        let μ := fairMeasure.prod (extMeasure extMean)
        μ {x | outcome P noOracle x.1 (fun a b => x.2 (a, b)) init = some true} =
          ENNReal.ofReal (Pd (lam : ℝ) y) ∧
        (∀ᵐ x ∂μ, outcome P noOracle x.1 (fun a b => x.2 (a, b)) init ≠ none) ∧
        ∫⁻ x, extCallCount P noOracle x.1 (fun a b => x.2 (a, b)) init ∂μ ≤ C ∧
        ∫⁻ x, wordWork P noOracle x.1 (fun a b => x.2 (a, b)) init ∂μ ≤ C) := by sorry

end HardCoreLocalSampling.Local
