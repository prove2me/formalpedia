-- Prove2me | Theorems.Thm_HarrisContact_MeanSize_time_scale_mean
-- name    : HarrisContact.MeanSize.time_scale_mean
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:24:59.846982+00:00
-- url     : https://prove2.me/theorems/87545f2c-81cd-42aa-b36e-dab29a0c6bf7
-- title:
--   Proof of Theorem 7.6, p. 982 — change of time scale: $m_t$ for rates $(c\mu, c\lambda_k)$ is $m_{ct}$ for $(\mu,\lambda_k)$
-- statement:
--   Let $m_t(\xi)$ denote the expected size at time $t$ of the contact process on $Z_d$ with death rate $\mu$ and birth rates $\lambda_k$, started from the finite set $\xi$. Multiplying every rate by a constant $c>0$ runs the same chain $c$ times faster: for every $t\ge0$ and every finite $\xi$,
--   $$m_t(\xi)\big|_{(c\mu,\,c\lambda_k)} = m_{ct}(\xi)\big|_{(\mu,\,\lambda_k)}.$$
--
--   This is the "change of time scale" by which the paper reduces Theorem 7.6, together with Lemma 5.8, to the case $\mu=1$, $\lambda_k=k\lambda$.
--
--   **Formalization Note** The identity is stated for the model's minimal transition function and holds for arbitrary real rates, so no contact hypotheses are imposed. The process is the countable-state chain on finite configurations of §4 (p. 975), with transition function the minimal solution $P_t$ of the backward equations for the rates (4.4)–(4.5); $m_t(\xi)=\sum_\eta P_t(\xi,\eta)\,|\eta|$ is an extended nonnegative real, so a divergent sum is $+\infty$, never $0$.
-- source:
--   Harris (Ann. Probab. 2, 1974), §7, proof of Theorem 7.6, p. 982 ('as in the proof of Theorem 7.1', a change of time scale; cf. proof of Theorem 7.1, p. 981)

import Mathlib
import Definitions.Def_HarrisContact_Extinction_Model
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HarrisContact.MeanSize

/-- Harris (Ann. Probab. 2, 1974), §7, proof of Theorem 7.6, p. 982 ("as in the proof of Theorem 7.1",
a change of time scale): multiplying every rate by `c > 0` runs the process `c` times faster, so
`m_t` for the rates `(cμ, cλ_k)` equals `m_{ct}` for `(μ, λ_k)`. -/
theorem time_scale_mean {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (c : ℝ) (hc : 0 < c) (t : ℝ) (ht : 0 ≤ t)
    (ξ : HarrisContact.Extinction.Config d) :
    HarrisContact.Extinction.meanSize (c * μ) (fun k => c * lam k) t ξ = HarrisContact.Extinction.meanSize μ lam (c * t) ξ := by sorry
end HarrisContact.MeanSize
