-- Prove2me | Theorems.Thm_NoRegretLastIterate_eq_3_20
-- name    : NoRegretLastIterate.eq_3_20
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:33:48.315901+00:00
-- url     : https://prove2.me/theorems/bf512378-ed5c-4de1-8a11-09b1e85d4f9b
-- title:
--   Eq. (3.19)–(3.20) — a monotonic mean-based optimal no-regret strategy leaves $p^*$ at distance $\beta/\sqrt{t_k}$ from $q^*$
-- statement:
--   Let $(G,H)$ satisfy condition (a) of Definition 2.6 with Nash equilibrium $(p^*,q^*)$, and let player 1 use a monotonic mean-based strategy $\{f_t\}$ with an optimal no-regret rate $(1/2,c)$. Then for every $0<\delta<(1-p^*)/3$ there are $\beta>0$ and a strictly increasing sequence $(t_k)$ such that for every $k$ one of the following holds:
--
--   1. $f_{t_k}(x)\ge p^*+\delta$ for all $x\in[0,1]$ with $x\ge q^*+\beta/\sqrt{t_k}$;
--   2. $f_{t_k}(x)\ge p^*+\delta$ for all $x\in[0,1]$ with $x\le q^*-\beta/\sqrt{t_k}$.
--
--   The first alternative is the printed (3.20), which the paper derives for non-decreasing $f_{t_k}$; the second is its mirror for non-increasing $f_{t_k}$. A deviation of the opponent's empirical average of order $1/\sqrt{t}$, in the appropriate direction, pushes player 1 a constant distance $\delta$ above her equilibrium strategy. The proof of Theorem 3.4 reuses this step.
--
--   **Formalization Note** In Lean $n_k=t_k-1$, so $f_{t_k}$ is `f (n k)` and $\sqrt{t_k}=\sqrt{n_k+1}$.
--
--   Differences from the source:
--   - generalization: "we will assume that f_t(·) is increasing in its argument without loss of generality" (p.10) and (3.20) f_{t_k}(x) ≥ p∗ + δ for all x ≥ q∗ + β/√t_k → for every k, (3.20) or its mirror f_{t_k}(x) ≥ p∗ + δ for all x ≤ q∗ − β/√t_k; reason: Definition 2.5 lets the direction change every round, so no single relabeling makes every f_{t_k} increasing; for non-decreasing f_{t_k} with q∗ − β/√t_k ≥ 0 the mirror implies (3.20), and since t_k → ∞ this holds from some k on, so a tail of the sequence gives the printed (3.20) for all k
--   - reading: β := α + γ₀ fixed in the proof, and "for all k ≥ 1" for the sequence of Proposition 3.1 restricted to k ≥ k₁ → ∃ β > 0 and a strictly increasing sequence t_k; reason: γ₀ comes from a CLT step of the proof; the statement asserts the bound for some fixed β along an infinite sequence
--   - reading: standing assumption "without loss of generality … condition (a)" (p.8) and (p∗, q∗) the NE → hypotheses CondA G H and IsNE G H (p∗, q∗); reason: the statement is made under the section's standing assumptions
--   - encoding: uniform no-regret rate (r, c) for a finite c: lim sup_T max_J T^{−r} Reg_T(J) ≤ c → ∃ c, for all large T and all J, Reg_T(J) ≤ c·T^r; reason: equivalent, since the maximum over {0,1}^T is finite; avoids a real-valued limsup
--   - encoding: rounds t = 1, 2, …; f_t applied to (J)^{t−1} → Lean rounds n = t − 1 from 0; F n applied to the first n actions; reason: Lean convention; same instances
--   - encoding: (p∗, q∗) a Nash equilibrium in mixed strategies; actions 0, 1 → published RankOneBimatrix.BinSearch.IsNE on the probability vectors (1 − p, p), (1 − q, q); actions Fin 2; reason: Lean convention and published vocabulary; same instances
-- source:
--   Muthukumar, Phade, Sahai, On the Impossibility of Convergence of Mixed Strategies with Optimal No-Regret Learning, arXiv:2012.02125v3, Eq. (3.19)–(3.20), proof of Theorem 3.3, pp.15–16; reused in the proof of Theorem 3.4, p.19

import Mathlib
import Definitions.Def_RankOneBimatrix_BinSearch_Game
import Definitions.Def_NoRegretLastIterate_Game
import Definitions.Def_NoRegretLastIterate_Strategy
import Definitions.Def_NoRegretLastIterate_MeanBased

namespace NoRegretLastIterate

/-- Muthukumar, Phade, Sahai, arXiv:2012.02125v3, Eq. (3.19)–(3.20), proof of Theorem 3.3,
pp.15–16, reused in the proof of Theorem 3.4 (p.19). Let `(G, H)` satisfy condition (a) of
Definition 2.6 (standing assumption, p.8) with Nash equilibrium `(p∗, q∗)`, and let player 1 use
a monotonic mean-based strategy `{f_t}` with an optimal no-regret rate `(1/2, c)`. Then for every
`0 < δ < (1 − p∗)/3` there are `β > 0` and a strictly increasing sequence `t_k` such that for
every `k`, either `f_{t_k}(x) ≥ p∗ + δ` for all `x ∈ [0, 1]` with `x ≥ q∗ + β/√t_k` (the printed
(3.20), for non-decreasing `f_{t_k}`), or `f_{t_k}(x) ≥ p∗ + δ` for all `x ∈ [0, 1]` with
`x ≤ q∗ − β/√t_k` (the mirror case, for non-increasing `f_{t_k}`).

**Formalization Note** Lean's `n k` is `t_k − 1`, so `f (n k)` is the paper's `f_{t_k}` and
`√t_k = √(n k + 1)`. The paper fixes "f_t increasing without loss of generality" (p.10); since the
direction of monotonicity may change every round (Definition 2.5), the statement is a disjunction
per `k`. -/
theorem eq_3_20 {G H : Matrix (Fin 2) (Fin 2) ℝ} (hA : CondA G H) {p q : ℝ}
    (hNE : RankOneBimatrix.BinSearch.IsNE G H (mix p) (mix q))
    {f : ℕ → ℝ → ℝ} (hf : IsMonotonicMeanBased f) (hrate : HasRate G (meanBased f) (1 / 2))
    (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < (1 - p) / 3) :
    ∃ β : ℝ, 0 < β ∧ ∃ n : ℕ → ℕ, StrictMono n ∧ ∀ k,
      (∀ x ∈ Set.Icc (0 : ℝ) 1, q + β / Real.sqrt ((n k : ℝ) + 1) ≤ x → p + δ ≤ f (n k) x) ∨
      (∀ x ∈ Set.Icc (0 : ℝ) 1, x ≤ q - β / Real.sqrt ((n k : ℝ) + 1) → p + δ ≤ f (n k) x) := by sorry

end NoRegretLastIterate
