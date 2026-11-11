-- Prove2me | Theorems.Thm_LargeSupplyFPA_Asymptotic_theorem_3
-- name    : LargeSupplyFPA.Asymptotic.theorem_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:03:50.130206+00:00
-- url     : https://prove2.me/theorems/33ecb9a3-4186-4f61-82b9-33ef8072cabb
-- title:
--   Theorem 3 — every $\epsilon$-approximate equilibrium has an atomless $(\epsilon+\omega)$-approximate equilibrium with the same welfare (and bids moved up by $<\omega$)
-- statement:
--   Consider any $k$-unit first-price auction with $n$ agents and independent value laws $V$, and any $\epsilon$-approximate Bayes–Nash equilibrium $E$. For every $\omega>0$ there is a strategy profile $\tilde E$ such that
--
--   (a) $\tilde E$ is an $(\epsilon+\omega)$-approximate Bayes–Nash equilibrium;
--
--   (b) for every agent $i$, the marginal bid distribution $\tilde E_i$ has no atoms;
--
--   (c) $W(E)=W(\tilde E)$;
--
--   (d) for every agent $i$, value $v$ and $t\in\mathbb R$, if $E_{i,v}((-\infty,t])=1$ then $\tilde E_{i,v}((-\infty,t+\omega])=1$.
--
--   Clause (d) is not printed in Theorem 3. It is what the proof of Theorem 2 uses on p. 28 ("by Assumption 2, $\tilde E^{(k)}$ satisfies Assumption 3"), and it follows from $\tilde b-b\in[0,\omega)$, shown in the proof of Theorem 3 on p. 33. So the welfare analysis can assume atomless equilibria at the cost of $\omega$ in the best-response slack.
--
--   Differences from the source:
--   - encoding: a strategy is a map E_i : V_i → Δ(ℝ≥0) from values to bid distributions → a Markov kernel E i : Kernel ℝ ℝ with E i v ((−∞, 0)) = 0 for every v; reason: measurability in v is what makes the marginal bid distribution ∫ E_{i,v} dV_i defined; a law on ℝ with no mass below 0 is a law on ℝ≥0
--   - reading: E_{b∼E_{i,v}}[u_i(v, b)] ≥ sup_{b≥0} u_i(v, b) − ϵ for every v ∈ supp(V_i) → for every v ∈ supp(V_i): b ↦ u_i(v, b) is E_{i,v}-integrable and u_i(v, b) − ϵ ≤ ∫ u_i(v, ·) dE_{i,v} for every b ≥ 0; reason: the ∀ b form is equivalent to the sup form; integrability makes explicit that the paper's expectation is finite (it holds automatically when bids are bounded on the support, as under Assumptions 2 and 3)
--   - generalization: conclusions (a)–(c) → (a)–(c) and a fourth clause (d): E_{i,v}((−∞, t]) = 1 implies Ẽ_{i,v}((−∞, t + ω]) = 1; reason: the proof of Theorem 2 needs that Ẽ over-bids by less than ω (p. 28), shown on p. 33; an extra conclusion specializes to the printed theorem
--   - encoding: a profile of bid distributions Ẽ → a strategy profile of Markov kernels Ẽ_i (values ↦ bid laws, bids ≥ 0); reason: (a) and (c) are statements about strategies, as in the paper's construction Ẽ_{i,v}
-- source:
--   Hartline, Shah, vonAllmen, Robust Analysis of First-Price Auctions with Large Supply, STOC 2027 submission (manuscript of November 3, 2026, sha256 2ad8363b…), p. 29, Theorem 3 (proof pp. 29–34)

import Mathlib
import Definitions.Def_LargeSupplyFPA_Asymptotic_Model
import Definitions.Def_LargeSupplyFPA_Asymptotic_Assumptions

open MeasureTheory ProbabilityTheory

namespace LargeSupplyFPA.Asymptotic

theorem theorem_3 {n : ℕ} (k : ℕ) (V : Fin n → Measure ℝ) (E : Fin n → Kernel ℝ ℝ) (ε : ℝ)
    (hV : IsValueProfile V) (hE : IsStrategyProfile E) (hBNE : IsApproxBNE k V E ε)
    (ω : ℝ) (hω : 0 < ω) :
    ∃ Et : Fin n → Kernel ℝ ℝ, IsStrategyProfile Et ∧
      IsApproxBNE k V Et (ε + ω) ∧
      IsAtomless V Et ∧
      welfare k V E = welfare k V Et ∧
      (∀ i v t, E i v (Set.Iic t) = 1 → Et i v (Set.Iic (t + ω)) = 1) := by sorry

end LargeSupplyFPA.Asymptotic
