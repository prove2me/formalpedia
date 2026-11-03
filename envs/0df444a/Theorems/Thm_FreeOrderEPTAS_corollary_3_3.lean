-- Prove2me | Theorems.Thm_FreeOrderEPTAS_corollary_3_3
-- name    : FreeOrderEPTAS.corollary_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:27:34.174953+00:00
-- url     : https://prove2.me/theorems/61d9bedf-30a6-4628-b461-4a63695329d3
-- title:
--   Corollary 3.3 — the assignment of every bucket load
-- statement:
--   There are $t$ and a universal $d$ such that, for $\epsilon=1/q$, $q\ge2$, at most $2q+1$ machines, non-negative guesses $b_i$ and any real $\Delta_i$, the program `santaClaus` at accuracy $\epsilon$ on the scaled instance with loads $\ell_{ij}=\mathbb E[\max\{X_j,b_i\}]-b_i$ satisfies:
--
--   1. if (IPProphets) is feasible then, with probability at least $1/2$, it returns a cardinality-feasible $x$ with
--   $$\sum_{j\in[n]}\ell_{ij}x_{ij}\ge(1-\epsilon)\Delta_i\quad\text{on every machine};$$
--   2. every returned $x$ has this property;
--   3. on every outcome the counted cost is at most $t(q)(n+1)^d$, and each instance has size at most $t(q)(n+1)$.
--
--   Scaling by $\Delta_i$ and truncating at $1$ loses nothing: one job with $\ell_{ij}\ge\Delta_i$ alone meets the bound.
--
--   Differences from the source:
--   - reading: "$t(\epsilon)\cdot\mathrm{poly}(n)$-time algorithm", with an oracle returning a real number and an LP solved inside → unit-cost real arithmetic, comparisons, floors, ceilings and logs; one counted call per oracle query, LP solve and rounding; instance sizes bounded by $t(\epsilon)(n+1)$; reason: the two primitives of the proof cannot both live in the bit model; with any polynomial LP solver and the polynomial GKPS procedure this gives $t(\epsilon)\cdot\mathrm{poly}(n)$
--   - reading: "There is an EPTAS for computing" an assignment → the randomized program, with probability at least $1/2$ when (IPProphets) is feasible; reason: the corollary follows from Theorem 2.1, which is randomized
--   - generalization: $2K+1$ machines → any $m\le2q+1$ machines, odd index meaning jump; reason: $2K+1\le2q+1$ by $K\le1/\epsilon$; covers the source’s case
--   - encoding: the load bound $\Delta_i$ and $\ell_{ij}$ in (IPProphets) → the normal form: active iff $\Delta_i>0$, loads $\ell_{ij}/\Delta_i$ truncated to $[0,1]$; reason: the scaling and truncation of p.8
--   - encoding: times and buckets $1,\dots,n$ and $1,\dots,2K+1$ → 0-based `Fin n`, `Fin (2K+1)`; even index stable, odd index jump; reason: a shift of indices; same objects
--   - encoding: $1/\epsilon$ an integer, p.17, with $\epsilon\in(0,1)$, p.9 → $\epsilon=1/q$ with $q\ge2$; reason: the same values of $\epsilon$
--   - encoding: BaseGuess enumerated over the non-negative grid of p.18 → hypothesis $b_i\ge0$; reason: the grid is non-negative
--   - generalization: DeltaGuess enumerated over the grid of p.18 → any real $\Delta_i$; a machine with $\Delta_i\le0$ is inactive; reason: grid values are covered; a non-positive bound is met by every assignment
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, Corollary 3.3, p.20

import Mathlib
import Definitions.Def_FreeOrderEPTAS_santaClaus
import Definitions.Def_FreeOrderEPTAS_prophetInstance
import Definitions.Def_FreeOrderEPTAS_IPProphets
import Definitions.Def_FreeOrderEPTAS_orc

namespace FreeOrderEPTAS

/-- Corollary 3.3, p.20 (arXiv:2007.13121v3), about `santaClaus` at accuracy `ϵ = 1/q` on the scaled
instance of §3.4, with `m ≤ 2q + 1` machines and loads `ℓ_ij = E[max{X_j, b_i}] - b_i`: when
(IPProphets) is feasible, with probability at least 1/2 the output is a cardinality-feasible `x`
with `∑_j ℓ_ij x_ij ≥ (1 - ϵ) Δ_i` on every machine; every output has this property; and the cost
and instance sizes are `t(q) (n + 1)^d` and `t(q) (n + 1)` on every outcome. -/
theorem corollary_3_3 :
    ∃ (t : ℕ → ℕ) (d : ℕ), ∀ (q : ℕ), 2 ≤ q → ∀ (m n : ℕ), m ≤ 2 * q + 1 →
      ∀ (I : Instance n) (b Δ : Fin m → ℝ), (∀ i, 0 ≤ b i) →
      ∀ (lp : LPSolver) (rnd : Rounding), IsLPSolver lp → IsDependentRounding rnd →
        (IPProphetsFeasible I b Δ → (1 / 2 : ℝ) ≤
          pr ((santaClaus (1 / (q : ℝ)) (prophetInstance (fun i j => orc I j (b i) - b i) Δ)
            lp rnd).run 0)
            {r | ∃ x, r.1 = some x ∧ ProphetCard x ∧
              ∀ i, (1 - 1 / (q : ℝ)) * Δ i ≤ ∑ j, excess I j (b i) * bit (x i j)}) ∧
        ∀ r ∈ ((santaClaus (1 / (q : ℝ)) (prophetInstance (fun i j => orc I j (b i) - b i) Δ)
            lp rnd).run 0).support,
          (∀ x, r.1 = some x → ProphetCard x ∧
            ∀ i, (1 - 1 / (q : ℝ)) * Δ i ≤ ∑ j, excess I j (b i) * bit (x i j)) ∧
          r.2.total ≤ t q * (n + 1) ^ d ∧ r.2.maxSize ≤ t q * (n + 1) := by sorry

end FreeOrderEPTAS
