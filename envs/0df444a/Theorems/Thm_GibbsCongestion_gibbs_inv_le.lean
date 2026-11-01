-- Prove2me | Theorems.Thm_GibbsCongestion_gibbs_inv_le
-- name    : GibbsCongestion.gibbs_inv_le
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:03:15.66098+00:00
-- url     : https://prove2.me/theorems/cf2aca23-b842-4a09-b30c-cb7be237eff9
-- title:
--   Inverse Gibbs probability: $\pi(s)^{-1}\le|\mathcal P|^n e^{T\Phi_{\max}}$ (corrected: sign of the exponent)
-- statement:
--   Throughout, $\Gamma$ is an extension parallel congestion game with common strategy set $\mathcal P$ (the $o,d$-paths of an EP network), $n\ge1$ players and non-negative, non-decreasing costs $c_e$; $T\ge0$ is the temperature, $\Phi$ is Rosenthal's potential, $\pi$ the Gibbs distribution, and $P$ the relaxed logit dynamics (with probability $\tfrac12$ two random distinct players swap strategies, with probability $\tfrac12$ a logit step).
--
--   For every strategy profile $s\in\mathcal P^n$,
--   $$\pi(s)^{-1}\ \le\ |\mathcal P|^n\,e^{T\Phi_{\max}},$$
--   because the cost functions, hence $\Phi$, are non-negative. This bounds the term $\log\log\pi(s)^{-1}$ in the mixing-time bound (7) by $\log(n\log|\mathcal P|+T\Phi_{\max})$.
--
--   Differences from the source:
--   - encoding: an extension parallel network G with o,d-path set P → a family P of arc sets with IsEPFamily P (single arc / parallel union / arc in series); reason: the game depends on the network only through its path family; the grammar generates exactly the path families of EP networks
--   - generalization: cost functions c_e : ℤ≥0 → ℚ, non-negative and non-decreasing → c : E → ℕ → ℝ, non-negative and monotone; reason: rational costs are real costs, so the statement specializes to the paper's
--   - encoding: N = [n] (players, [k] defined for k ∈ ℤ>0) → hypothesis 0 < n; reason: the paper's implicit n ≥ 1
--   - correction: π(s)⁻¹ ≤ |P|ⁿ e^{−TΦmax} → π(s)⁻¹ ≤ |P|ⁿ e^{TΦmax}; reason: false as printed: n = 1, two parallel arcs, c ≡ 1, T = 1 give π(s)⁻¹ = 2 > 2/e
-- source:
--   Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §4.2, p.18

import Mathlib
import Definitions.Def_GibbsCongestion_IsEPFamily
import Definitions.Def_GibbsCongestion_potentialMax
import Definitions.Def_GibbsCongestion_gibbs

namespace GibbsCongestion

/-- **Bound on the inverse Gibbs probability, corrected** (Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §4.2, p.18). For every profile
`s ∈ Pⁿ`, `π(s)⁻¹ ≤ |P|ⁿ e^{TΦmax}`, because the costs are non-negative.

**Correction** The paper prints `π(s)⁻¹ ≤ |P|ⁿ e^{−TΦmax}`, false for `n = 1`, two parallel arcs,
`c ≡ 1`, `T = 1` (`π(s)⁻¹ = 2 > 2/e`). The sign of the exponent is corrected.

**Formalization Note** The network is encoded by its family `P` of o,d-paths (`IsEPFamily`);
players are `Fin n` with `0 < n`; profiles are `s : Fin n → P`. Costs are real valued,
non-negative and non-decreasing (the paper's standing assumption, p.7, with `ℚ` generalized to
`ℝ`). -/
theorem gibbs_inv_le {E : Type*} [Fintype E] [DecidableEq E]
    (P : Finset (Finset E)) (hP : IsEPFamily P) (n : ℕ) (hn : 0 < n)
    (c : E → ℕ → ℝ) (hc_nonneg : ∀ e k, 0 ≤ c e k) (hc_mono : ∀ e, Monotone (c e)) (T : ℝ) (hT : 0 ≤ T) (s : Fin n → P) :
    (gibbs P n c T s)⁻¹ ≤ (P.card : ℝ) ^ n * Real.exp (T * potentialMax P n c) := by sorry

end GibbsCongestion
