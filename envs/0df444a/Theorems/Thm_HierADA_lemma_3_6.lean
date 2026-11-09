-- Prove2me | Theorems.Thm_HierADA_lemma_3_6
-- name    : HierADA.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T18:00:12.330865+00:00
-- url     : https://prove2.me/theorems/6f973e3b-0804-45e3-a76e-ea544fd9d9c5
-- title:
--   Lemma 3.6 — projection and sensitivity
-- statement:
--   Fix a threshold $\tau>0$ and a block of size $r\ge1$.
--
--   1. For every score vector $G\in\mathbb R^r$ there is $c\in\mathbb R$ such that the vector
--   $$
--   w_i=\frac1r\,\mathrm{clip}_{[0,8]}\Big(\frac\tau4G_i+c\Big),\qquad\mathrm{clip}_{[0,8]}(x)=\min(8,\max(0,x)),
--   $$
--   sums to one, lies in $W$, maximizes the objective of Equation (2) over $W$, and equals the weights $w(G)$ of Equation (2).
--   2. For fixed $G:U\to\mathbb R$ and $f:U\to[0,1]$, the weighted prediction $h(S)=\sum_iw_i(G(X_1),\dots,G(X_r))\,f(X_i)$ has global sensitivity at most $16/r$: $|h(S)-h(S')|\le\frac{16}r$ whenever $S,S'$ differ in one sample.
--
--   The closed form identifies the update as a shifted, clipped projection, and the sensitivity bound is what the Laplace mechanism and AboveThreshold need in the privacy analysis (Theorem 3.7).
--
--   **Formalization Note** "Differ in one sample" is the published `PrivLearn.Generic.Neighbors`, and $W$ is the published `NondualOpt.cappedSimplex r 8`.
--
--   Differences from the source:
--   - encoding: a block of size r; the threshold τ = α/(4p) → 1 ≤ r and 0 < τ; reason: the lemma's setting
--   - encoding: “the weights in Equation (2) satisfy (14) … c is chosen so that the weights sum to one” → there is c with Σ_i w_i = 1, the vector lies in W, maximizes (2), and equals regWeights; reason: the three clauses are what “satisfy” asserts; regWeights is the maximizer of (2)
-- source:
--   Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams, preprint (version of 2026-11-03, sha256 f220ae51…), Lemma 3.6, p.23, Equation (14)

import Mathlib
import Definitions.Def_IsRandomnessNecessaryADA_Plain_Protocol
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_NondualOpt_cappedSimplex
import Definitions.Def_HierADA_objective
import Definitions.Def_HierADA_regWeights

set_option autoImplicit false

open IsRandomnessNecessaryADA.Plain

namespace HierADA

/-- **Lemma 3.6 (Projection and sensitivity)** — Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, *Adaptive
Data Analysis and Adversarial Robustness on Insertion-Deletion Streams*, preprint (version of
2026-11-03, sha256 f220ae51…), Lemma 3.6, p.23, Equation (14).

For a block of size `r ≥ 1` and a threshold `τ > 0`:
1. for every score vector `G ∈ ℝ^r` there is `c ∈ ℝ` such that the vector
   `w_i = (1/r) clip_{[0,8]}((τ/4) G_i + c)`, with `clip_{[0,8]}(x) = min(8, max(0, x))`, sums to one,
   lies in `W`, maximizes the objective of Equation (2) over `W`, and is the weight vector `w(G)`;
2. for fixed `G : U → ℝ` and `f : U → [0, 1]`, the weighted prediction
   `h(S) = ∑_i w_i(G(X_1), …, G(X_r)) f(X_i)` has global sensitivity at most `16/r`:
   `|h(S) − h(S')| ≤ 16/r` for datasets `S, S'` differing in one sample.

**Formalization Note.** "Differing in one sample" is the published `PrivLearn.Generic.Neighbors`
(Definition 2.3). `τ > 0` is the paper's `τ = α/(4p)`. -/
theorem lemma_3_6 (τ : ℝ) (hτ : 0 < τ) (r : ℕ) (hr : 1 ≤ r) :
    (∀ G : Fin r → ℝ, ∃ c : ℝ,
      ∑ i, 1 / (r : ℝ) * min 8 (max 0 (τ / 4 * G i + c)) = 1 ∧
      (fun i => 1 / (r : ℝ) * min 8 (max 0 (τ / 4 * G i + c))) ∈ NondualOpt.cappedSimplex r 8 ∧
      (∀ v ∈ NondualOpt.cappedSimplex r 8, objective τ r G v ≤
        objective τ r G fun i => 1 / (r : ℝ) * min 8 (max 0 (τ / 4 * G i + c))) ∧
      regWeights τ r G = fun i => 1 / (r : ℝ) * min 8 (max 0 (τ / 4 * G i + c))) ∧
    ∀ {U : Type} (G : U → ℝ) (f : StatisticalQuery U) (s s' : Fin r → U),
      PrivLearn.Generic.Neighbors s s' →
        |∑ i, regWeights τ r (fun i => G (s i)) i * (f (s i) : ℝ) -
            ∑ i, regWeights τ r (fun i => G (s' i)) i * (f (s' i) : ℝ)| ≤ 16 / r := by sorry

end HierADA
