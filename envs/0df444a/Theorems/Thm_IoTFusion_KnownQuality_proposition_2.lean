-- Prove2me | Theorems.Thm_IoTFusion_KnownQuality_proposition_2
-- name    : IoTFusion.KnownQuality.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:19:19.754099+00:00
-- url     : https://prove2.me/theorems/4190f828-12a2-4795-b891-e2a1c48c4426
-- title:
--   Proposition 2, p. 15 — familiarity dynamics: ψ grows by the stickiness factor f(q_i, q_j) per targeting, so ψ = initial familiarity + f · target count (15)
-- statement:
--   Let sensor $i$ follow the target rule along a sample path $S_\infty = (s_0, s_1, \dots)$, and let $\psi_{ijt}$ be its familiarity function with sensor $j$ in period $t$, $f(q_i,q_j)$ the stickiness factor and $a_{ijt} \in \{0,1\}$ the indicator that $i$ targets $j$ in period $t$. Then for every $s \in \mathbb R$:
--
--   1. $\psi_{ij,t+1}(s) = \psi_{ijt}(s) + f(q_i,q_j)\,a_{ijt}$, with $f(q_i,q_j) = \dfrac{1+q_i^2}{q_j^2(1+q_i^2+q_j^2)}$ (14);
--   2. for all $t = 1, 2, 3, \dots$,
--   $$\psi_{ij,t+1}(s) = \frac{v_{ij0}^2 w_{ij0}^2}{w_{ij0}^2 + v_{ij0}^2 s^2} + f(q_i,q_j) \sum_{l=1}^{t} a_{ijl}. \qquad (15)$$
--
--   Part 2 says that the familiarity depends on the history only through the number of times $j$ has been targeted, not on when. It is the closed form on which Remark 1, Lemma 2 and Proposition 4 rest.
--
--   **Formalization Note** Lean step $k$ is the paper's period $k+1$. Part 2 is stated for every $k \ge 0$ (at $k = 0$ the sum is empty and the identity is (12)). Because the mission defines the familiarity by (12) and the update (14), part 1 is the defining recursion; the content is part 2. No positivity hypotheses are needed.
-- source:
--   Saghafian, Tomlin, Biller, The Internet of Things and Information Fusion: Who Talks to Who?, SSRN 3124417 (version of October 16, 2020), p. 15, Proposition 2 (14)–(15)

import Mathlib
import Definitions.Def_IoTFusion_KnownQuality_Model

namespace IoTFusion.KnownQuality

/-- **Proposition 2 (Familiarity Dynamics)**, Saghafian, Tomlin, Biller, The Internet of Things and Information Fusion: Who Talks to Who?, SSRN 3124417 (version of October 16, 2020), p. 15.

For every state value `x`: (i) the familiarity of `i` with `j` grows from one step to the next by
the stickiness factor `f(q_i, q_j)` (14) exactly when `j` is the current target; (ii) it equals the
initial familiarity (12) plus `f(q_i, q_j)` times the number of times `j` has been targeted (15).

**Formalization Note.** Lean step `k` is the paper's period `k + 1`: `fam P i s k` is
`ψ_{ij,k+1}`, `target P i s k` is `j*_{i,k+1}` and `count P i s j k` is `Σ_{l=1}^{k} a_{ijl}`.
The paper's (15) is stated for `t ≥ 1`; part (ii) here holds for every `k`, including `k = 0`
(empty sum). Since `ψ` is defined by (12) and the update (14) (the paper's familiarity dynamics),
part (i) is the defining recursion. No positivity hypotheses are needed. -/
theorem proposition_2 {n : ℕ} (P : Instance n) (i j : Fin n) (s : ℕ → ℝ) (x : ℝ) :
    (∀ k : ℕ, fam P i s (k + 1) j x =
      fam P i s k j x + stick (P.q i) (P.q j) * (if target P i s k = j then 1 else 0)) ∧
    (∀ k : ℕ, fam P i s k j x = psi1 P i j x + stick (P.q i) (P.q j) * (count P i s j k : ℝ)) := by sorry

end IoTFusion.KnownQuality
