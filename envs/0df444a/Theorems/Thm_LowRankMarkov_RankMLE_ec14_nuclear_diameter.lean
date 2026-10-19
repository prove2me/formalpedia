-- Prove2me | Theorems.Thm_LowRankMarkov_RankMLE_ec14_nuclear_diameter
-- name    : LowRankMarkov.RankMLE.ec14_nuclear_diameter
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:27:12.191676+00:00
-- url     : https://prove2.me/theorems/76795768-d7e2-40f5-9b2f-5a40b5c87ff5
-- title:
--   (EC.14), ec9 — on the shell 𝒞_l, ‖Q − P‖_* ≤ 2β(2^l η r/(pαπ_min))^{1/2}
-- statement:
--   Let $\alpha,\beta>0$, let $P$ be a primitive transition matrix satisfying Assumption 1 with $\operatorname{rank}(P)=r$, and let $\pi$ be its stationary probability vector with all $\pi_i>0$. Let $l\ge1$ and $\eta>0$. If $Q$ is feasible for the rank-constrained problem (5) ($Q1_p=1_p$, $\alpha/p\le Q_{ij}\le\beta/p$, $\operatorname{rank}(Q)\le r$) and $Q\in\mathcal C$ with $D_{\mathrm{KL}}(P,Q)\ge\eta$, where $\mathcal C$ is the cone class on p. 14, and
--   $$2^{l-1}\eta\le D_{\mathrm{KL}}(P,Q)\le 2^l\eta ,$$
--   then
--   $$\|Q-P\|_*\ \le\ 2\beta\Big(\frac{2^l\eta r}{p\alpha\pi_{\min}}\Big)^{1/2}.$$
--
--   In the proof of Lemma 3 the set of candidate matrices is split into the shells $\mathcal C_l$ cut out by the two KL inequalities above; this bound on the nuclear-norm radius of each shell controls the Rademacher complexity of the empirical KL process on it.
--
--   **Formalization Note** The paper bounds $\sup_{Q\in\mathcal C_l}\|Q-P\|_*$; the statement gives the equivalent pointwise upper bound for each member of the shell, avoiding a supremum over an empty set. The shell includes the printed class $\mathcal C$, $D_{\mathrm{KL}}(P,Q)\ge\eta$, $l\ge1$, and the rank constraint. $2^{l-1}$ is a real power with integer exponent.
-- source:
--   Zhu, Li, Wang & Zhang, Learning Markov Models via Low-Rank Optimization, arXiv:1907.00113v2, p. ec9 (PDF p. 42), (EC.14); shells C_l, p. ec8 (PDF p. 41)

import Mathlib
import Definitions.Def_CaiCandesShen_Convergence_Basic
import Definitions.Def_LowRankMarkov_RankMLE_Chain
import Definitions.Def_LowRankMarkov_RankMLE_Setting

namespace LowRankMarkov.RankMLE

open CaiCandesShen.Convergence

/-- (EC.14), ec9, arXiv:1907.00113v2: under Assumption 1, every `Q` of the shell
`𝒞_l = {Q ∈ 𝒞(η) : 2^{l−1}η ≤ D_KL(P, Q) ≤ 2^l η, rank(Q) ≤ r}` satisfies
`‖Q − P‖_* ≤ 2β (2^l η r/(pαπ_min))^{1/2}` (the supremum over `𝒞_l`, stated pointwise). -/
theorem ec14_nuclear_diameter {p r : ℕ} (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (P Q : Matrix (Fin p) (Fin p) ℝ) (π : Fin p → ℝ)
    (hP : IsStochastic P) (hprim : IsPrimitive P) (hA1 : Assumption1 α β r P)
    (hπ : IsStationary π P) (hπ_pos : ∀ i, 0 < π i)
    (l : ℕ) (hl : 1 ≤ l) (η : ℝ) (hη : 0 < η)
    (hQ : RankFeasible α β r Q) (hC : ConcentrationClass α β P Q)
    (hηQ : η ≤ klDiv π P Q)
    (hlow : (2 : ℝ) ^ ((l : ℤ) - 1) * η ≤ klDiv π P Q)
    (hup : klDiv π P Q ≤ (2 : ℝ) ^ l * η) :
    nuclearNorm (Q - P) ≤ 2 * β * Real.sqrt ((2 : ℝ) ^ l * η * r / (p * α * piMin π)) := by sorry

end LowRankMarkov.RankMLE
