-- Prove2me | Theorems.Thm_NoRegretLastIterate_lemma_3_2
-- name    : NoRegretLastIterate.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:33:08.309752+00:00
-- url     : https://prove2.me/theorems/2b804ee6-3f4a-4f03-8c90-09a79879e9db
-- title:
--   Lemma 3.2 — against i.i.d. Bernoulli$(q^*)$ play, any self-agnostic strategy earns $tR^*$ in expectation
-- statement:
--   Let $(G,H)$ satisfy condition (a) of Definition 2.6 and let $(p^*,q^*)$ be its Nash equilibrium, with equilibrium payoff $R^*=G(p^*,q^*)$. Let $J^*_1,J^*_2,\dots$ be i.i.d. Bernoulli$(q^*)$ random variables and let $\{f_s\}$ be any self-agnostic strategy of player 1. Then for every $t\ge1$,
--   $$
--   \mathbb E\Big[\sum_{s=1}^t G\big(f_s((J^*)^{s-1}),J^*_s\big)\Big]=tR^*\qquad\text{and}\qquad \mathbb E\Big[\sum_{s=1}^tJ^*_s\Big]=tq^* .
--   $$
--
--   Against an opponent who plays the equilibrium mixed strategy independently each round, no self-agnostic strategy gains or loses in expectation relative to the equilibrium payoff. This is the baseline against which Proposition 3.1 measures the effect of a late burst of action 1.
--
--   **Formalization Note** $G(f,J^*_s)$ is the bilinear extension at $(f,\mathbf 1\{J^*_s=1\})$. Independence is `iIndepFun`, and each $J^*_n$ has $\mu(J^*_n=1)=q^*$.
--
--   Differences from the source:
--   - reading: standing assumption "without loss of generality … condition (a)" (p.8) and (p∗, q∗) the NE → hypotheses CondA G H and IsNE G H (p∗, q∗); reason: the statement is made under the section's standing assumptions
--   - reading: "the sequence {J∗_s}_{s≥1} defined above" (i.i.d. Bernoulli(q∗), inside the proof of Proposition 3.1) → any measurable i.i.d. Bernoulli(q∗) sequence on any probability space (iIndepFun and μ{J∗_n = 1} = q∗); reason: the lemma uses only the i.i.d. Bernoulli(q∗) law of the sequence
--   - encoding: (p∗, q∗) a Nash equilibrium in mixed strategies; actions 0, 1 → published RankOneBimatrix.BinSearch.IsNE on the probability vectors (1 − p, p), (1 − q, q); actions Fin 2; reason: Lean convention and published vocabulary; same instances
--   - encoding: rounds t = 1, 2, …; f_t applied to (J)^{t−1} → Lean rounds n = t − 1 from 0; F n applied to the first n actions; reason: Lean convention; same instances
-- source:
--   Muthukumar, Phade, Sahai, On the Impossibility of Convergence of Mixed Strategies with Optimal No-Regret Learning, arXiv:2012.02125v3, Lemma 3.2, (3.7a)–(3.7b), p.11

import Mathlib
import Definitions.Def_RankOneBimatrix_BinSearch_Game
import Definitions.Def_NoRegretLastIterate_Game
import Definitions.Def_NoRegretLastIterate_Strategy

open MeasureTheory ProbabilityTheory

namespace NoRegretLastIterate

/-- Muthukumar, Phade, Sahai, arXiv:2012.02125v3, Lemma 3.2, p.11. Let `(G, H)` satisfy
condition (a) of Definition 2.6 (the paper's standing assumption from p.8) and let `(p∗, q∗)` be
its Nash equilibrium, with `R∗ := G(p∗, q∗)`. Let `J∗_1, J∗_2, …` be i.i.d. Bernoulli(`q∗`) and
`{f_s}` any self-agnostic strategy of player 1. Then for every `t ≥ 1`,
`E[Σ_{s=1}^t G(f_s((J∗)^{s−1}), J∗_s)] = t R∗` (3.7a) and `E[Σ_{s=1}^t J∗_s] = t q∗` (3.7b).

**Formalization Note** Lean rounds `0, …, t − 1` are the paper's rounds `1, …, t`; `F n` is the
paper's `f_{n+1}`. `G(f, J∗_s)` is the bilinear extension `ext G f (bit J∗_s)` (expected payoff
over player 1's coin). The Nash equilibrium is the published predicate
`RankOneBimatrix.BinSearch.IsNE` applied to the probability vectors `(1 − p, p)`, `(1 − q, q)`. -/
theorem lemma_3_2 {G H : Matrix (Fin 2) (Fin 2) ℝ} (hA : CondA G H) {p q : ℝ}
    (hNE : RankOneBimatrix.BinSearch.IsNE G H (mix p) (mix q))
    {F : (n : ℕ) → (Fin n → Fin 2) → ℝ} (hF : IsStrategy F)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Js : ℕ → Ω → Fin 2) (hmeas : ∀ n, Measurable (Js n)) (hind : iIndepFun Js μ)
    (hlaw : ∀ n, μ {ω | Js n ω = 1} = ENNReal.ofReal q) (t : ℕ) (ht : 1 ≤ t) :
    ∫ ω, ∑ n ∈ Finset.range t, ext G (F n (fun k : Fin n => Js k ω)) (bit (Js n ω)) ∂μ
        = t * ext G p q ∧
      ∫ ω, ∑ n ∈ Finset.range t, bit (Js n ω) ∂μ = t * q := by sorry

end NoRegretLastIterate
