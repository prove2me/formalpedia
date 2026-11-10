-- Prove2me | Theorems.Thm_LocalOccupancyIS_Glauber_proposition_6
-- name    : LocalOccupancyIS.Glauber.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:58:58.709286+00:00
-- url     : https://prove2.me/theorems/b0a6c24a-27b1-4a87-b85c-84e78825ba80
-- title:
--   Proposition 6 — explicit local occupancy and uniform asymptotics
-- statement:
--   Let $t\ge1$ be an integer, $b\ge0$ and $\Delta\ge1$. Suppose the finite graph $G$ has every degree at most $\Delta$ and hereditary neighborhood $K_{t,t}$-density at most $b$. Define $s,\rho,D,\lambda,M,c$ as in the parameter definition and suppose $D\ge8et$. With $p=\lambda/(1+\lambda)$, for every $0\le w\le D$ there is local occupancy at the computed parameters
--
--   $$\beta_w=\frac{e^w}{p(1+w)},\qquad\gamma_w=\frac1{c(1+w)}.$$
--
--   For $z=W(p\Delta/c)$,
--
--   $$0<z<D,\qquad\Gamma=\beta_z+\gamma_z\Delta=\frac\Delta{cz}.$$
--
--   For every admissible parameter sequence, one absolute constant, chosen before the sequence, eventually bounds
--
--   $$\left|\frac{\Gamma D}{\Delta}-1\right|\le A\frac{t\log D}{D}.$$
--
--   The whole finite parameter family and the uniform asymptotic assertion are required; the latter does not assume any graph-dependent error constant. This supplies the local occupancy parameters for the goal.
--
--   Differences from the source:
--   - encoding: finite independent sets and induced subgraphs → Boolean configurations on finite types and induced subtypes; reason: these presentations preserve all feasible configurations, including the empty one
--   - encoding: uniform O(t log D/D) as D tends to infinity and t log D=o(D) → one positive absolute constant before all admissible natural-indexed families, with an eventual absolute relative-error inequality; reason: the family convention makes the source uniformity explicit; graph degree bounds in the finite clause may be real
-- source:
--   Ewan Davies, Brian Tan, STOC 2027 submission #982 (October 2026), Proposition 6, p. 10–12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/982.pdf#page=10

import Definitions.Def_LocalOccupancyIS_Glauber_Parameters

namespace LocalOccupancyIS.Glauber
/-- Proposition 6, pp.10–12, finite family and absolute uniform sequence asymptotics. -/
theorem proposition_6 :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (Δ : ℝ) (t : ℕ) (b : ℝ), 1 ≤ Δ → 1 ≤ t → 0 ≤ b → (∀ v, (G.degree v : ℝ) ≤ Δ) →
      HereditaryDensity G t b → 8 * Real.exp 1 * t ≤ D Δ t b →
      let lam := fugacity Δ t b
      let c := correction Δ t b
      let z := optimizer Δ lam c
      (∀ w : ℝ, 0 ≤ w → w ≤ D Δ t b → LocalOccupancy G lam (beta lam w) (gamma c w)) ∧
      0 < z ∧ z < D Δ t b ∧ Gamma Δ lam c = Δ / (c*z)) ∧
    (∃ A : ℝ, 0 < A ∧ ∀ (Δ : ℕ → ℝ) (t : ℕ → ℕ) (b : ℕ → ℝ), AdmissibleReal Δ t b →
      ∀ᶠ i in Filter.atTop,
        |Gamma (Δ i) (fugacity (Δ i) (t i) (b i)) (correction (Δ i) (t i) (b i)) *
          D (Δ i) (t i) (b i) / Δ i - 1| ≤ A * relativeError (Δ i) (t i) (b i)) := by sorry
end LocalOccupancyIS.Glauber
