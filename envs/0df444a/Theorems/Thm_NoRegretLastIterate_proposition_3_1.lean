-- Prove2me | Theorems.Thm_NoRegretLastIterate_proposition_3_1
-- name    : NoRegretLastIterate.proposition_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:33:52.926154+00:00
-- url     : https://prove2.me/theorems/f0468554-d3c8-4185-9c77-1e4d837d4205
-- title:
--   Proposition 3.1 — fluctuation sensitivity of rate-$(r,c)$ no-regret strategies (corrected: (3.4) needs $\delta<p^*/3$)
-- statement:
--   Let $(G,H)$ satisfy condition (a) of Definition 2.6 with Nash equilibrium $(p^*,q^*)$, and let $\{f_t\}$ be a self-agnostic strategy of player 1 that is uniformly no-regret with a rate $(r,c)$, $\frac12\le r<1$. For a pair $(t,s)$ let $J'$ be the history whose first $t-s$ entries are i.i.d. Bernoulli$(q^*)$ and whose remaining entries equal $1$, and $J''$ the same with $0$ in place of $1$.
--
--   1. For every $0<\delta<(1-p^*)/3$ there are $\alpha>0$ and integer pairs $(t_k,s_k)_{k\ge1}$ with $t_k$ strictly increasing such that for all $k$
--   $$
--   0<s_k\le\alpha\,t_k^{\,r}\qquad\text{and}\qquad \mathbb E\big[f_{t_k}(J'_1,\dots,J'_{t_k-1})\big]\ge p^*+2\delta .
--   $$
--   2. For every $0<\delta<p^*/3$ there are $\alpha>0$ and $(t_k,s_k)_{k\ge1}$ with $t_k$ strictly increasing such that for all $k$
--   $$
--   0<s_k\le\alpha\,t_k^{\,r}\qquad\text{and}\qquad \mathbb E\big[f_{t_k}(J''_1,\dots,J''_{t_k-1})\big]\le p^*-2\delta .
--   $$
--
--   An opponent who plays the equilibrium for most of the time and then switches to a constant action for only $O(t^r)$ rounds moves the strategy's expected play a constant distance away from $p^*$, infinitely often. With $r=1/2$ the burst shifts the opponent's empirical average by only $O(1/\sqrt t)$, which is the order of its natural fluctuations.
--
--   **Formalization Note** In Lean the round index is $n_k=t_k-1$ and the expectation is the finite sum `perturbedMean` with Bernoulli product weights; the length of the i.i.d. block is $t_k-s_k$ (natural-number subtraction, an empty block when $s_k\ge t_k$).
--
--   Differences from the source:
--   - correction: (3.4) for every 0 < δ < (1 − p∗)/3 → (3.4) for every 0 < δ < p∗/3; reason: f_t ≥ 0, so (3.4) fails whenever 2δ > p∗: take G matching pennies and H = [[0, 1], [9, 0]] (condition (a), p∗ = 0.1, q∗ = 1/2), δ = 0.2 < 0.3 = (1 − p∗)/3, and any rate-(1/2, c) strategy such as Hedge; then p∗ − 2δ = −0.3 < 0 ≤ E[f]. "Similarly" is read as the mirror of (3.2) (actions 0 ↔ 1 in the burst of player 2, p∗ ↔ 1 − p∗), whose range is δ < (G(0,0) − R∗)/(3(G(0,0) − G(1,0))) = p∗/3. For p∗ < 1/2 this also leaves out δ ∈ [p∗/3, min(p∗/2, (1 − p∗)/3)), where the printed clause is not refuted by the counterexample but is not the mirror of anything the paper claims or proves
--   - generalization: for p∗ > 1/2, (3.4) for 0 < δ < (1 − p∗)/3 → (3.4) for every 0 < δ < p∗/3, a wider range; reason: the mirror of (3.2) holds on the mirrored range δ < p∗/3, which contains (1 − p∗)/3 when p∗ ≥ 1/2, so the clause specializes to the printed one there
--   - reading: (3.4) printed as E[f_{t_k}((J′(k))^{t_k})] → expectation over J″(k); reason: the sentence after (3.4) says the expectation is over (J″(k))^{t_k}
--   - reading: f_{t_k}((J′(k))^{t_k}), a history of length t_k → f_{t_k} applied to the first t_k − 1 entries of J′(k) (resp. J″(k)); reason: Definition 2.1 makes f_t a function of t − 1 actions, and the proof evaluates f_{t∗+s}((J′)^{t∗+s−1}) with t_k = t∗ + s_k (pp.12–13)
--   - reading: "an infinite sequence of integer tuples {(t_k, s_k)}" → t_k strictly increasing; reason: the proof's t_k = t∗(t₁ + k) + s_k tends to infinity, so a strictly increasing subsequence exists; a bounded sequence would say nothing about large t (strong reading)
--   - reading: "Similarly, we also have (3.4)" → clause 2 has its own α and its own sequence (t_k, s_k); reason: the proof constructs the sequence for (3.2) only; "similarly" is the mirror argument, which produces a second sequence
--   - reading: standing assumption "without loss of generality … condition (a)" (p.8) and (p∗, q∗) the NE → hypotheses CondA G H and IsNE G H (p∗, q∗); reason: the statement is made under the section's standing assumptions
--   - encoding: uniform no-regret rate (r, c) for a finite c: lim sup_T max_J T^{−r} Reg_T(J) ≤ c → ∃ c, for all large T and all J, Reg_T(J) ≤ c·T^r; reason: equivalent, since the maximum over {0,1}^T is finite; avoids a real-valued limsup
--   - encoding: E over J′_s(k) i.i.d. Bernoulli(q∗) for 1 ≤ s ≤ t_k − s_k and constant otherwise; index t_k → perturbedMean F q∗ (n k) (n k + 1 − s k) b with n k = t_k − 1; reason: the expectation written as a finite sum with Bernoulli product weights; same value
--   - encoding: (p∗, q∗) a Nash equilibrium in mixed strategies; actions 0, 1 → published RankOneBimatrix.BinSearch.IsNE on the probability vectors (1 − p, p), (1 − q, q); actions Fin 2; reason: Lean convention and published vocabulary; same instances
-- source:
--   Muthukumar, Phade, Sahai, On the Impossibility of Convergence of Mixed Strategies with Optimal No-Regret Learning, arXiv:2012.02125v3, Proposition 3.1, (3.1)–(3.5), pp.9–10 (proof pp.10–13)

import Mathlib
import Definitions.Def_RankOneBimatrix_BinSearch_Game
import Definitions.Def_NoRegretLastIterate_Game
import Definitions.Def_NoRegretLastIterate_Strategy
import Definitions.Def_NoRegretLastIterate_PerturbedMean

namespace NoRegretLastIterate

/-- Muthukumar, Phade, Sahai, arXiv:2012.02125v3, Proposition 3.1, pp.9–10 (corrected: the
(3.4) clause requires `δ < p∗/3`). Let `(G, H)` satisfy condition (a) of Definition 2.6 (standing
assumption, p.8) with Nash equilibrium `(p∗, q∗)`, and let `{f_t}` be a self-agnostic strategy of
player 1 that is uniformly no-regret with a rate of `(r, c)`, `1/2 ≤ r < 1`.

1. For every `0 < δ < (1 − p∗)/3` there are `α > 0` and integer tuples `(t_k, s_k)`, `t_k`
   strictly increasing, with `0 < s_k ≤ α t_k^r` (3.1) and `E[f_{t_k}(J′(k))] ≥ p∗ + 2δ` (3.2),
   where `J′_s(k)` is i.i.d. Bernoulli(`q∗`) for `1 ≤ s ≤ t_k − s_k` and `1` otherwise (3.3).
2. For every `0 < δ < p∗/3` there are `α > 0` and `(t_k, s_k)` as above with
   `E[f_{t_k}(J″(k))] ≤ p∗ − 2δ` (3.4), where `J″` is as `J′` but with `0` in place of `1` (3.5).

**Formalization Note** Lean's `n k` is `t_k − 1`: `F (n k)` is the paper's `f_{t_k}`, applied to
the first `t_k − 1` entries of `J′(k)` (how the proof uses it, pp.12–13); the i.i.d. block has
length `t_k − s_k = n k + 1 − s k` (natural-number subtraction; the block is empty when
`s_k ≥ t_k`). `perturbedMean` is the expectation, written as a finite sum with Bernoulli product
weights. The two clauses carry their own `α` and sequence. The printed (3.4) has the bound
`δ < (1 − p∗)/3` of the first clause; it is false when `2δ > p∗` because `f_t ≥ 0`. -/
theorem proposition_3_1 {G H : Matrix (Fin 2) (Fin 2) ℝ} (hA : CondA G H) {p q : ℝ}
    (hNE : RankOneBimatrix.BinSearch.IsNE G H (mix p) (mix q))
    {F : (n : ℕ) → (Fin n → Fin 2) → ℝ} (hF : IsStrategy F)
    {r : ℝ} (hr : 1 / 2 ≤ r ∧ r < 1) (hrate : HasRate G F r) :
    (∀ δ : ℝ, 0 < δ → δ < (1 - p) / 3 →
      ∃ α : ℝ, 0 < α ∧ ∃ n s : ℕ → ℕ, StrictMono n ∧ ∀ k,
        0 < s k ∧ (s k : ℝ) ≤ α * ((n k : ℝ) + 1) ^ r ∧
          p + 2 * δ ≤ perturbedMean F q (n k) (n k + 1 - s k) 1) ∧
    (∀ δ : ℝ, 0 < δ → δ < p / 3 →
      ∃ α : ℝ, 0 < α ∧ ∃ n s : ℕ → ℕ, StrictMono n ∧ ∀ k,
        0 < s k ∧ (s k : ℝ) ≤ α * ((n k : ℝ) + 1) ^ r ∧
          perturbedMean F q (n k) (n k + 1 - s k) 0 ≤ p - 2 * δ) := by sorry

end NoRegretLastIterate
