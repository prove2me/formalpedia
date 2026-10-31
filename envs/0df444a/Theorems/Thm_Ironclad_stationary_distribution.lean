-- Prove2me | Theorems.Thm_Ironclad_stationary_distribution
-- name    : Ironclad.stationary_distribution
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:26:26.064996+00:00
-- url     : https://prove2.me/theorems/353c757c-4dea-4188-a257-6f5c372d2c1c
-- title:
--   Appendix .2.2 — the stationary distribution $\pi$ of the embedded chain
-- statement:
--   Let $0<p_h<1$, $0<q<1$, $\Delta\ge1$, $q_h=(1-q)p_h$, $q_H=qp_h$, and
--
--   $$
--   \pi_0=\frac{q_H(1-q_H)^\Delta+q_h(1-q_H)^\Delta(1-p_h)^\Delta}{q_H+q_h(1-q_H)^\Delta},\quad \pi_1=\frac{q_h(1-q_H)^\Delta(1-(1-p_h)^\Delta)}{q_H+q_h(1-q_H)^\Delta},\quad \pi_2=\frac{q_H(1-(1-q_H)^\Delta)}{q_H+q_h(1-q_H)^\Delta}.
--   $$
--
--   Then $\pi$ is the stationary distribution of the embedded chain with transition matrix (3):
--
--   1. $\pi_i\ge0$ for every $i$ and $\pi_0+\pi_1+\pi_2=1$;
--   2. $\pi P=\pi$;
--   3. $\pi$ is the only vector with properties 1 and 2.
--
--   The weights $\pi_i$ enter every long-run frequency in the proof of Lemma 3.1.
--
--   Differences from the source:
--   - reading: "stationary distribution" → a probability vector with $\pi P=\pi$, and the unique one; reason: the definite article; uniqueness holds because (3) is primitive
--   - reading: no parameter range in App. .2.2 → $0<p_h<1$, $0<q<1$, $\Delta\ge1$; reason: the proper parameters of Theorem 3.2
-- source:
--   Zhang, Gong, Li, Wu & Zhang, Improving Blockchain Consistency by Assigning Weights to Random Blocks, arXiv:2107.10467v2, Appendix .2.2, p.30, for the matrix (3) of p.10

import Mathlib
import Definitions.Def_Ironclad_ClosedForms

namespace Ironclad

/-- The stationary distribution of the embedded Markov chain, Zhang, Gong, Li, Wu & Zhang,
*Improving Blockchain Consistency by Assigning Weights to Random Blocks*, arXiv:2107.10467v2, Appendix .2.2, p.30: the vector `π` of p.30 is the stationary distribution of the embedded
chain: it is a probability vector, `π P = π` for the transition matrix (3), and it is the only
probability vector with this property.

**Formalization Note** The standing parameter range `0 < p_h, q < 1`, `Δ ≥ 1` is that of
Theorem 3.2. -/
theorem stationary_distribution (ph q : ℝ) (Δ : ℕ) (hph0 : 0 < ph) (hph1 : ph < 1) (hq0 : 0 < q)
    (hq1 : q < 1) (hΔ : 1 ≤ Δ) :
    (∀ i, 0 ≤ piStat ph q Δ i) ∧ ∑ i, piStat ph q Δ i = 1 ∧
    Matrix.vecMul (piStat ph q Δ) (Pmat ph q Δ) = piStat ph q Δ ∧
    ∀ ν : Fin 3 → ℝ, (∀ i, 0 ≤ ν i) → ∑ i, ν i = 1 → Matrix.vecMul ν (Pmat ph q Δ) = ν →
      ν = piStat ph q Δ := by sorry

end Ironclad
