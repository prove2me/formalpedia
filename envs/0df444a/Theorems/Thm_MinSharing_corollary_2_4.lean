-- Prove2me | Theorems.Thm_MinSharing_corollary_2_4
-- name    : MinSharing.corollary_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:25:05.550562+00:00
-- url     : https://prove2.me/theorems/568c8a7e-5035-4f60-89b8-19a58f6618e3
-- title:
--   Corollary 2.4 — threshold structure of fPO allocations between two agents
-- statement:
--   Let $z$ be a fractionally Pareto-optimal allocation for a valuation matrix $v$ of arbitrary signs. There are weights $\lambda_1,\dots,\lambda_n>0$ such that for every pair of agents $i\ne j$ the threshold $t_{i,j}=\lambda_j/\lambda_i>0$ satisfies, for every object $o$:
--
--   1. if $v_{i,o}v_{j,o}>0$ (both agents agree whether $o$ is a good or a bad): when $|v_{i,o}|/|v_{j,o}|>t_{i,j}$, then $z_{j,o}=0$ for a good and $z_{i,o}=0$ for a bad; when $|v_{i,o}|/|v_{j,o}|<t_{i,j}$, then $z_{i,o}=0$ for a good and $z_{j,o}=0$ for a bad;
--   2. if $v_{i,o}v_{j,o}<0$, the agent with negative value does not consume $o$;
--   3. if $v_{i,o}=0$ but $v_{j,o}\ne0$, then $z_{j,o}=0$ when $v_{j,o}<0$ and $z_{i,o}=0$ when $v_{j,o}>0$;
--   4. in particular, if $o$ is shared between $i$ and $j$ ($z_{i,o}>0$ and $z_{j,o}>0$), then
--   $$\frac{v_{i,o}}{v_{j,o}}=t_{i,j}\qquad\text{or}\qquad v_{i,o}=v_{j,o}=0 .$$
--
--   For two agents this describes every fPO allocation by one threshold on the value ratios, which is the basis of the enumeration of Lemma 3.8 and of the reduction in the proof of Theorem 3.6(b).
--
--   Differences from the source:
--   - generalization: for each pair i ≠ j there is a threshold t_{i,j} > 0 (t_{i,j} = λ_j/λ_i from Lemma 2.3) → one weight vector λ > 0 with t_{i,j} = λ_j/λ_i for all pairs simultaneously; reason: this is the corollary's own parenthetical; choosing t_{i,j} := λ_j/λ_i gives the per-pair statement
--   - encoding: "in the case of a good / of a bad" when v_{i,o}·v_{j,o} > 0 → v_{i,o} > 0 / v_{i,o} < 0; reason: both agents' values have the same sign
--   - encoding: o shared between i and j; v_{i,o}/v_{j,o} = t_{i,j} → z_{i,o} > 0 ∧ z_{j,o} > 0; v_{j,o} ≠ 0 ∧ v_{i,o}/v_{j,o} = t_{i,j}; reason: the ratio is only written when it is defined
--   - encoding: agents [n] = {1,…,n}, objects [m] = {1,…,m} → Fin n, Fin m (paper index = Lean index + 1); reason: Lean convention; same instances
-- source:
--   Sandomirskiy, Segal-Halevi, Efficient Fair Division with Minimal Sharing, arXiv:1908.01669v3, Corollary 2.4, p.10

import Mathlib
import Definitions.Def_CompetitiveChores_RichFamily_Setting

set_option autoImplicit false

namespace MinSharing

open CompetitiveChores.RichFamily

/-- **Corollary 2.4** (Sandomirskiy, Segal-Halevi, arXiv:1908.01669v3, p.10). For a fractionally
Pareto-optimal allocation `z` and any pair of agents `i ≠ j` there is a threshold `t_{i,j} > 0`
(`t_{i,j} = λⱼ/λᵢ` from Lemma 2.3) such that for every object `o`:
* if `vᵢ,ₒ · vⱼ,ₒ > 0`: for `|vᵢ,ₒ|/|vⱼ,ₒ| > t_{i,j}`, `zⱼ,ₒ = 0` for a good and `zᵢ,ₒ = 0` for a bad;
  for `|vᵢ,ₒ|/|vⱼ,ₒ| < t_{i,j}`, `zᵢ,ₒ = 0` for a good and `zⱼ,ₒ = 0` for a bad;
* if `vᵢ,ₒ · vⱼ,ₒ < 0`, the agent with negative value does not consume `o`;
* if `vᵢ,ₒ = 0` but `vⱼ,ₒ ≠ 0`: `zⱼ,ₒ = 0` for negative `vⱼ,ₒ`, `zᵢ,ₒ = 0` for positive `vⱼ,ₒ`;
* in particular, `o` can be shared between `i` and `j` only if `vᵢ,ₒ/vⱼ,ₒ = t_{i,j}` or
  `vᵢ,ₒ = vⱼ,ₒ = 0`.

**Formalization Note** The thresholds come from one weight vector `w` (the `λ` of Lemma 2.3):
`t_{i,j} = w j / w i` for every pair, as the parenthetical of the corollary says. When
`vᵢ,ₒ · vⱼ,ₒ > 0`, "good" is `vᵢ,ₒ > 0` and "bad" is `vᵢ,ₒ < 0` (both agents agree). "Shared between
`i` and `j`" is `zᵢ,ₒ > 0 ∧ zⱼ,ₒ > 0`. -/
theorem corollary_2_4 {n m : ℕ} (v z : Fin n → Fin m → ℝ) (hz : IsParetoOptimal v z) :
    ∃ w : Fin n → ℝ, (∀ i, 0 < w i) ∧
      ∀ i j : Fin n, i ≠ j → 0 < w j / w i ∧ ∀ o : Fin m,
        (0 < v i o * v j o →
          (w j / w i < |v i o| / |v j o| → (0 < v i o → z j o = 0) ∧ (v i o < 0 → z i o = 0)) ∧
          (|v i o| / |v j o| < w j / w i → (0 < v i o → z i o = 0) ∧ (v i o < 0 → z j o = 0))) ∧
        (v i o * v j o < 0 → (v i o < 0 → z i o = 0) ∧ (v j o < 0 → z j o = 0)) ∧
        (v i o = 0 → v j o ≠ 0 → (v j o < 0 → z j o = 0) ∧ (0 < v j o → z i o = 0)) ∧
        (0 < z i o → 0 < z j o →
          (v j o ≠ 0 ∧ v i o / v j o = w j / w i) ∨ (v i o = 0 ∧ v j o = 0)) := by sorry

end MinSharing
