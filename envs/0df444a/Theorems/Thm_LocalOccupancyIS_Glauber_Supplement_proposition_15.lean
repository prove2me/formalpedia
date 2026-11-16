-- Prove2me | Theorems.Thm_LocalOccupancyIS_Glauber_Supplement_proposition_15
-- name    : LocalOccupancyIS.Glauber.Supplement.proposition_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T22:04:12.957484+00:00
-- url     : https://prove2.me/theorems/70d926bb-4f89-4926-9545-a0b032669bde
-- title:
--   Proposition 15 — uniform chromatic local occupancy
-- statement:
--   Consider arbitrary sequences $\Delta_i\ge3$, integers $t_i\ge1$, and $b_i\ge0$ such that the appendix parameters satisfy $H_i\to\infty$ and $t_i\log H_i/H_i\to0$. Use exactly $\lambda_A,c_A,q,z_0,\epsilon_A,a_A,\beta_A,\gamma_A$ defined by (29), (31) and Proposition 15, including the integer floor in $a_A$.
--
--   There is one absolute constant $A>0$, chosen before all such families, such that eventually $0<q<1$, $a_A\ge1$,
--
--   $$\beta_A=\frac{e^{z_0}}p=\frac{(1+\lambda_A)\Delta}{LH^3},\qquad \gamma_A=\frac1{qa_A},\qquad |\gamma_AH-1|\le A\left(\sqrt{\frac{\log H}{H}}+\frac{t\log H}{H}\right).$$
--
--   At the same eventual indices, every finite graph of degree at most $\Delta$ and hereditary $K_{t,t}$-density at most $b$ in neighborhoods has $q$-chromatic local $(\beta_A,\gamma_A)$-occupancy at fugacity $\lambda_A$. The occupancy disjunction holds for every subgraph, with arbitrary edge deletions and its own vertex set. The error constant is independent of $b,t$, the parameter family, and the graph; the eventual threshold may depend on the family but is uniform over its graphs.
--
--   Differences from the source:
--   - encoding: the absolute uniform O-term in the regime H→∞ and t log H=o(H) → one absolute A before all admissible sequences, followed by eventual graph-uniform assertions and |γH−1|≤A E_A; reason: this spells out the stated asymptotic quantifiers; no finite instance is replaced by a special case
-- source:
--   Ewan Davies, Brian Tan, STOC 2027 submission #982 (October 2026), p.24, Proposition 15, equation (36)

import Definitions.Def_LocalOccupancyIS_Glauber_Supplement_Correspondence

namespace LocalOccupancyIS.Glauber.Supplement
/-- Proposition 15, p.24. One absolute constant precedes all parameter families
and every graph. Eventual thresholds may depend on the family, not on its graph. -/
theorem proposition_15 :
    ∃ A : ℝ, 0 < A ∧
    ∀ (Δ : ℕ → ℝ) (t : ℕ → ℕ) (b : ℕ → ℝ), AppAdmissible Δ t b →
      ∀ᶠ i in Filter.atTop,
        let lam := appLam (Δ i) (t i) (b i)
        let H := appH (Δ i) (t i) (b i)
        let q := appQ (Δ i) (t i) (b i)
        let β := appBeta (Δ i) (t i) (b i)
        let γ := appGamma (Δ i) (t i) (b i)
        0 < q ∧ q < 1 ∧ 1 ≤ appA (Δ i) (t i) (b i) ∧
        β = (1+lam) * Δ i / (appL (Δ i) * H^3) ∧
        |γ * H - 1| ≤ A * appError (Δ i) (t i) (b i) ∧
        ∀ {V : Type} [Fintype V] [DecidableEq V],
          ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
            RealDegreeBound G (Δ i) → HereditaryDensity G (t i) (b i) →
              ChromaticOccupancy G lam q β γ := by sorry
end LocalOccupancyIS.Glauber.Supplement
