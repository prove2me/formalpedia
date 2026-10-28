-- Prove2me | Theorems.Thm_LiquidDemocracy_Upward_eq_14
-- name    : LiquidDemocracy.Upward.eq_14
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:24:31.160545+00:00
-- url     : https://prove2.me/theorems/4fbb80e2-d99b-404e-a036-168fc8cbee33
-- title:
--   (14), proof of Lemma 1, p. 37 — gain(p⃗_n, G_n) ≥ −ℙ[X^D_n > X^F_{G_n}]
-- statement:
--   Let $n$ voters have competencies $p_1,\dots,p_n\in[0,1]$, and let $G_n$ be any delegation graph on them. With $X^D_n$ and $X^F_{G_n}$ the numbers of correct votes under direct and liquid democracy, the gain of the instance satisfies
--
--   $$\mathrm{gain}(\vec p_n,G_n)\ \ge\ -\,\mathbb P_{\vec p_n}\big[X^D_n>X^F_{G_n}\big].$$
--
--   Liquid democracy can therefore lose against direct democracy only by as much as the probability that it gets strictly fewer correct votes. This is the first step of the proof of Lemma 1: it reduces do no harm to showing that $X^F_{G_n}\ge X^D_n$ with high probability.
--
--   **Formalization Note** The statement is deterministic in the instance; $p_i\in[0,1]$ is the standing assumption of p. 9, needed for $\mathbb P_{\vec p_n}$ to be a probability.
-- source:
--   Berinsky et al., Tracking Truth with Liquid Democracy, arXiv:2107.11868v3, p. 37, proof of Lemma 1 (Appendix B.1), (14)

import Mathlib
import Definitions.Def_LiquidDemocracy_Upward_Setting

namespace LiquidDemocracy.Upward

/-- (14), proof of Lemma 1 (Appendix B.1), p. 37: for every instance with competencies in `[0,1]`,
`gain(p⃗_n, G_n) ≥ −ℙ_{p⃗_n}[X^D_n > X^F_{G_n}]`. -/
theorem eq_14 (n : ℕ) (c : Fin n → ℝ) (hc : ∀ i, c i ∈ Set.Icc (0 : ℝ) 1) (g : DelegGraph n) :
    -voteProb c (fun v => XF g v < XD v) ≤ gain c g := by sorry

end LiquidDemocracy.Upward
