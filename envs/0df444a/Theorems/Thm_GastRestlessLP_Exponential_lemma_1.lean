-- Prove2me | Theorems.Thm_GastRestlessLP_Exponential_lemma_1
-- name    : GastRestlessLP.Exponential.lemma_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T00:18:36.884712+00:00
-- url     : https://prove2.me/theorems/efdbda46-fda9-4157-8901-23263e71dfdc
-- title:
--   Lemma 1 — one-step mean, expected L1 error, and exponential concentration
-- statement:
--   Fix a finite nonempty state space of size $d$, a stochastic two-action arm model, and $N>0$. For any current labeled state assignment $x$ and realized action assignment $a$, let $Y$ be their empirical occupation vector. Draw the next states independently with transition probabilities $P^{a_i}_{x_i,s'}$, and put $E=M'-\phi(Y)$. Then all three conclusions hold:
--   $$\mathbb E[E_s]=0\quad\text{for every }s,$$
--   $$\mathbb E[\|E\|_1]\le\frac{\sqrt d}{\sqrt N},$$
--   $$\mathbb P(\|E\|_1\ge\varepsilon)\le 2d\exp(-2N\varepsilon^2/d^2)\quad(\varepsilon\ge0).$$
--   For every attainable state-action count vector these are the source's conditional assertions (8)–(10). All actions are covered, without a restriction to priority policies, an optimal trajectory, or an integer budget. The statement supplies the full one-step fluctuation control used by the paper.
--
--   Differences from the source:
--   - encoding: states labeled 1 through d and actions 0,1 → an arbitrary finite nonempty state type with decidable equality and actions Fin 2; reason: finite relabeling preserves every source instance and d is its cardinality
--   - reading: the allocation factor in (7) is printed with destination subscript s → phi uses departure subscript r in the sum over r,a; reason: (4b) and the conditional mean identity on p. 5 uniquely specify this intended reading; see I1
--   - generalization: conditional assertions at the realized state-action counts of the controlled process → all fixed labeled state and action assignments under their explicit product transition law; reason: this includes every attainable count-conditioned distribution; relabeling does not change the empirical next-state law and averaging over assignments with the same counts preserves all three clauses
--   - encoding: expectations and probabilities conditional on Y and a concentration radius epsilon → finite weighted sums and every nonnegative real epsilon, including zero; reason: the finite conditional laws avoid choosing versions on probability-zero conditioning events; nonnegative radii are the concentration convention
-- source:
--   Gast, Gaujal and Yan, arXiv:2106.10067v3 (22 December 2023), https://arxiv.org/abs/2106.10067v3, Lemma 1, p. 7, equations (8)–(10)

import Definitions.Def_GastRestlessLP_Exponential_Population

open scoped BigOperators

namespace GastRestlessLP.Exponential

theorem lemma_1 {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (M : Model S) (N : ℕ) (hN : 0 < N) (x : Fin N → S) (a : Fin N → Fin 2) :
    (∀ s, (transitionLaw M x a).expect (fun x' => transitionError M x a x' s) = 0) ∧
    (transitionLaw M x a).expect (fun x' => l1 (transitionError M x a x')) ≤
      Real.sqrt (Fintype.card S : ℝ) / Real.sqrt (N : ℝ) ∧
    (∀ ε : ℝ, 0 ≤ ε →
      probability (transitionLaw M x a) (fun x' => ε ≤ l1 (transitionError M x a x')) ≤
        2 * (Fintype.card S : ℝ) *
          Real.exp (-2 * (N : ℝ) * ε ^ 2 / (Fintype.card S : ℝ) ^ 2)) := by sorry

end GastRestlessLP.Exponential
