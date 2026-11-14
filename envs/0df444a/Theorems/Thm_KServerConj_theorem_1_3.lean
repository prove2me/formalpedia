-- Prove2me | Theorems.Thm_KServerConj_theorem_1_3
-- name    : KServerConj.theorem_1_3
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T16:51:53.7822+00:00
-- url     : https://prove2.me/theorems/886b8e9f-1e71-41f4-b232-e9fd24166da8
-- title:
--   Theorem 1.3 — the $k$-server conjecture: $\mathrm{WFA}_{C_0}(\varrho)\le k\,\mathrm{OPT}_{C_0}(\varrho)+\mathrm{cl}(C_0)$
-- statement:
--   Let $(M,d)$ be any pseudometric space (finite or infinite), $k\ge1$, and $C_0$ an initial configuration of $k$ points. For every finite request sequence $\varrho=(r_1,\dots,r_T)$:
--
--   1. the Work Function Algorithm is well defined: there is a WFA trajectory $C_0,C_1,\dots,C_T$, each $C_t$ a configuration of $k$ points containing $r_t$ and minimizing $w_t(C)+D(C_{t-1},C)$ over all such configurations;
--   2. every WFA trajectory, with any tie-breaking rule, satisfies
--
--   $$\mathrm{WFA}_{C_0}(\varrho)\le k\,\mathrm{OPT}_{C_0}(\varrho)+\mathrm{cl}(C_0),$$
--
--   where $\mathrm{WFA}_{C_0}(\varrho)=\sum_{t=1}^T D(C_{t-1},C_t)$, $\mathrm{OPT}_{C_0}(\varrho)$ is the optimal offline cost, and $\mathrm{cl}(C_0)$ is the clique weight of $C_0$.
--
--   The Work Function Algorithm is therefore $k$-competitive on every metric space. Since no deterministic online algorithm is better than $k$-competitive on a space with more than $k$ points (Manasse, McGeoch, Sleator 1988), this settles the $k$-server conjecture.
--
--   Differences from the source:
--   - generalization: a metric space (M, d) → a pseudometric space (`PseudoMetricSpace M`); reason: the paper, p.1: "our proof works also when d is a pseudometric"; every metric space is a pseudometric space
--   - generalization: the work function algorithm (defined with a lazy tie-break C_t ⊆ C_{t−1} ∪ {r_t}) → every trajectory of minimizers of w_t(C) + D(C_{t−1}, C) over all configurations C ∋ r_t (IsWFATraj); reason: p.2: "our result extends to any other tie-breaking rule"; the lazy trajectory is one of them
--   - generalization: the statement presupposes that WFA is defined → an added clause: a WFA trajectory exists; reason: an added conclusion, which also rules out a bound that holds because no trajectory satisfies the predicate
--   - encoding: k servers → hypothesis 1 ≤ k and C₀.card = k; reason: for k = 0 no configuration contains a request, so the algorithm is undefined; configurations are k-element sets
--   - encoding: a finite request sequence r₁, …, r_T → r : ℕ → M, with requests r 1, …, r T; reason: values of r outside 1, …, T enter no quantity of the statement
--   - encoding: OPT_{C₀}(r₁, …, r_T) = min_X w_T(X) → the infimum of the costs of offline schedules (opt); reason: the same number: the offline optimum ends in some configuration X and costs w_T(X)
--   - encoding: configurations {x₁, …, x_k} and D(X, Y) = min over permutations → Finset M with card k; D as the infimum over bijections X ≃ Y; reason: the same objects
-- source:
--   Coester, Koutsoupias, Zbysiński, The k-server conjecture is true, arXiv:2609.15979 (version of 2026-11-03, sha256 7ca0380a…), Theorem 1.3, p.2 (pdf p.3)

import Mathlib
import Definitions.Def_KServerConj_cl
import Definitions.Def_KServerConj_opt
import Definitions.Def_KServerConj_IsWFATraj

namespace KServerConj

/-- **Theorem 1.3 (the k-server conjecture).** Coester, Koutsoupias, Zbysiński, *The k-server
conjecture is true*, arXiv:2609.15979 (version of 2026-11-03, sha256 7ca0380a…), printed p.2
(PDF p.3): "Let (M, d) be any metric space, and let C₀ = {s₁, …, s_k} be the initial
configuration. For every finite request sequence ϱ, the work function algorithm satisfies
WFA_{C₀}(ϱ) ≤ k OPT_{C₀}(ϱ) + cl(C₀)."

Two clauses: a trajectory of the Work Function Algorithm exists, and every trajectory, whatever its
tie-break, costs at most `k · OPT + cl(C₀)` on the requests `r 1, …, r T`.

**Formalization Note.** `M` is an arbitrary, possibly infinite, type with a pseudometric (the paper,
printed p.1: "our proof works also when d is a pseudometric"). Configurations are finite sets of
`k` points with `k ≥ 1`. `OPT` is the infimum of the cost of offline schedules (`opt`), the
paper's `min_X w_T(X)`; the trajectory cost is `wfaCost`; the matching distance is `confDist` (1). -/
theorem theorem_1_3 {M : Type*} [PseudoMetricSpace M] (k : ℕ) (hk : 1 ≤ k)
    (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M) (T : ℕ) :
    (∃ C : ℕ → Finset M, IsWFATraj k C₀ r T C) ∧
    ∀ C : ℕ → Finset M, IsWFATraj k C₀ r T C →
      wfaCost C T ≤ (k : ℝ) * opt k C₀ r T + cl C₀ := by sorry

end KServerConj
