-- Prove2me | Theorems.Thm_LocalOccupancyIS_Glauber_Supplement_theorem_16
-- name    : LocalOccupancyIS.Glauber.Supplement.theorem_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T22:05:00.825028+00:00
-- url     : https://prove2.me/theorems/db943644-2c18-4ef6-9d7e-9412fd8c04ec
-- title:
--   Theorem 16 — correspondence coloring with constant one
-- statement:
--   Let $\Delta\ge3$, integer $t\ge1$ and $b\ge0$ vary along any family, and put
--
--   $$H=\log\frac{\Delta}{(b+1)^{1/(2t-1)}(\log\Delta)^t},\qquad E_A=\sqrt{\frac{\log H}{H}}+\frac{t\log H}{H}.$$
--
--   There is an absolute $A>0$, independent of every family, $b,t$ and graph, such that if $H\to\infty$ and $t\log H/H\to0$, then eventually every finite graph $G$ of degree at most $\Delta$ and hereditary neighborhood $K_{t,t}$-density at most $b$ satisfies
--
--   $$\chi_c(G)\le(1+A E_A)\frac{\Delta}{H}.$$
--
--   Both specializations are included: if $b\ge0$ is fixed and $t=o(\log\Delta/\log\log\Delta)$, or if $t\ge1$ is fixed and $\log(b+1)/\log\Delta\to0$, then, for every $\zeta>0$, eventually
--
--   $$\chi_c(G)\le(1+\zeta)\frac{\Delta}{\log\Delta}.$$
--
--   All eventual bounds quantify over every graph satisfying the hypotheses, including empty graphs and graphs with low-degree vertices. Correspondence coloring quantifies over arbitrary partial matchings and independent list relabelings. There is no minimum-degree assumption, no supplied coloring framework axiom, and no assumed chromatic bound. The finite colorable list size in the conclusion also guarantees the bound is attained by a valid integer size.
--
--   Differences from the source:
--   - encoding: the absolute uniform upper O-bound and both o(1) specializations for χ_c → an absolute A preceding all admissible sequences, and eventual finite colorable-list-size bounds; each specialization is quantified for every ζ>0; reason: the list-size witness is equivalent to the upper bound for the least universally colorable size and avoids converting an infinite infimum to zero
-- source:
--   Ewan Davies, Brian Tan, STOC 2027 submission #982 (October 2026), pp.24–25, Theorem 16

import Definitions.Def_LocalOccupancyIS_Glauber_Supplement_Correspondence

namespace LocalOccupancyIS.Glauber.Supplement
/-- Theorem 16, pp.24–25, including both leading-constant-one specializations.
The error constant is chosen before all families; ColoringBound quantifies over
all partial-matching correspondence assignments, and asserts an actual finite bound. -/
theorem theorem_16 :
    (∃ A : ℝ, 0 < A ∧
      ∀ (Δ : ℕ → ℝ) (t : ℕ → ℕ) (b : ℕ → ℝ), AppAdmissible Δ t b →
        ∀ᶠ i in Filter.atTop,
          ∀ {V : Type} [Fintype V] [DecidableEq V],
            ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
              RealDegreeBound G (Δ i) → HereditaryDensity G (t i) (b i) →
                ColoringBound G ((1 + A * appError (Δ i) (t i) (b i)) *
                  Δ i / appH (Δ i) (t i) (b i))) ∧
    (∀ (b : ℝ), 0 ≤ b → ∀ (Δ : ℕ → ℝ) (t : ℕ → ℕ),
      (∀ i, 3 ≤ Δ i ∧ 1 ≤ t i) →
      Filter.Tendsto Δ Filter.atTop Filter.atTop →
      Filter.Tendsto (fun i => (t i : ℝ) * Real.log (Real.log (Δ i)) /
        Real.log (Δ i)) Filter.atTop (nhds 0) →
      ∀ ζ : ℝ, 0 < ζ → ∀ᶠ i in Filter.atTop,
        ∀ {V : Type} [Fintype V] [DecidableEq V],
          ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
            RealDegreeBound G (Δ i) → HereditaryDensity G (t i) b →
              ColoringBound G ((1+ζ) * Δ i / Real.log (Δ i))) ∧
    (∀ (t : ℕ), 1 ≤ t → ∀ (Δ b : ℕ → ℝ),
      (∀ i, 3 ≤ Δ i ∧ 0 ≤ b i) →
      Filter.Tendsto Δ Filter.atTop Filter.atTop →
      Filter.Tendsto (fun i => Real.log (b i + 1) / Real.log (Δ i))
        Filter.atTop (nhds 0) →
      ∀ ζ : ℝ, 0 < ζ → ∀ᶠ i in Filter.atTop,
        ∀ {V : Type} [Fintype V] [DecidableEq V],
          ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
            RealDegreeBound G (Δ i) → HereditaryDensity G t (b i) →
              ColoringBound G ((1+ζ) * Δ i / Real.log (Δ i))) := by sorry
end LocalOccupancyIS.Glauber.Supplement
