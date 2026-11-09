-- Prove2me | Theorems.Thm_LocalPush_lemma_5_3
-- name    : LocalPush.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:07:34.872201+00:00
-- url     : https://prove2.me/theorems/a6bfbaf6-f2d8-4ae2-82d2-a51927e70f77
-- title:
--   Lemma 5.3, clauses on $\mathcal G$ (Pr part: lemma_5_3_prob) — at most $1/\lambda$ iterations, nonnegativity, $x_i>0.9\alpha\kappa$, $\mathrm{vol}(S_i)\le1/\lambda$, (17)
-- statement:
--   Assume the parameters of Algorithm 3 with $(\lambda+\eta)d(s)<1$ on a graph without isolated nodes, and consider a good trajectory reaching iterations $0,\dots,N$: every solver output $\tilde x_i$ satisfies (6) and the stopping rule fails at iterations $0,\dots,N-1$. Write $x_i=x^{(S_i)}$, $p_i=Dx_i$, $r_i=r(x_i)$, $\tilde p_i=D\tilde x_i$, $\tilde r_i=r(\tilde x_i)$ and $\mathcal T_i=S_{i+1}\setminus S_i$. Then:
--
--   1. $N+1\le1/\lambda$, so on $\mathcal G$ the algorithm terminates after at most $1/\lambda$ iterations;
--   2. for every $i\le N$: $x_i,p_i,r_i,\tilde x_i,\tilde p_i,\tilde r_i\ge0$, $x_i(v)>0.9\alpha\kappa$ for every $v\in S_i$, and $\mathrm{vol}(S_i)\le1/\lambda$;
--   3. for every $i<N$: $x_{i+1}\ge x_i$ and
--   $$r_i(v)>(\lambda+0.9\kappa)d(v)\ \ \forall v\in\mathcal T_i,\qquad r_i(v)\le(\lambda+1.1\kappa)d(v)\ \ \forall v\notin S_{i+1};\tag{17}$$
--   4. if the stopping rule holds at $N$, the returned $\tilde p=D\tilde x_N$ satisfies $\tilde p\ge0$ and $0\le r(D^{-1}\tilde p)\le(\lambda+\eta)d$.
--
--   These are the invariants of the active-set process that the rest of the analysis uses; item 4 is the ACL guarantee of the output.
--
--   Differences from the source:
--   - encoding: Lemma 5.3 as one statement: Pr{𝒢} ≥ 1 − δ, and the clauses on 𝒢 → the clauses on 𝒢 here; Pr{𝒢} ≥ 1 − δ is the separate milestone LocalPush.lemma_5_3_prob; reason: the two parts live in different models (good trajectories vs. a seed space); together they are the lemma
--   - encoding: "On 𝒢, Algorithm 3 terminates after at most 1/λ iterations" → every good trajectory has N + 1 ≤ 1/λ; reason: a run on 𝒢 that reached more than 1/λ iterations would have a good prefix violating the bound, so the two are equivalent
--   - encoding: Algorithm 3 run with a randomized SDD solver, conditioned on 𝒢 → a relation over solver outputs: every output x̃_i (extended by zero off S_i) satisfying (6) is allowed; line 7's r̃ on ∂S is written r(x̃); reason: on 𝒢 the only property of the solver outputs the paper uses is (6); r̃ = r(x̃) on ∂S by eq. (10)
-- source:
--   Cui, Wei, Yang, Revisiting Local Push, STOC 2027 submission (manuscript sha256 4c36279a…), §5.1, Lemma 5.3, p.19 (PDF p.19)

import Mathlib
import Definitions.Def_LocalPush_GoodTraj

open Finset Matrix

namespace LocalPush

/-- **Lemma 5.3, the clauses on the good event `𝒢`.**

Cui, Wei, Yang, *Revisiting Local Push: Faster Algorithms and Optimal Query Complexity for PageRank and
Effective Resistance*, STOC 2027 submission (manuscript sha256 4c36279a…), §5.1, Lemma 5.3, p.19 (PDF p.19).

"On 𝒢, Algorithm 3 terminates after at most 1/λ iterations and returns p̃ ≥ 0 with 0 ≤ r(D⁻¹p̃) ≤ (λ + η)d.
Moreover, on 𝒢, for every iteration i, we have x_i, p_i, r_i, x̃_i, p̃_i, r̃_i ≥ 0, x_i(v) > 0.9ακ for every
v ∈ 𝒮_i, and vol(𝒮_i) ≤ 1/λ. On 𝒢, whenever the stopping rule is not met at iteration i, we have
x_{i+1} ≥ x_i, and r_i(v) > (λ + 0.9κ)d(v), ∀ v ∈ 𝒯_i, r_i(v) ≤ (λ + 1.1κ)d(v), ∀ v ∉ 𝒮_{i+1}. (17)"

For every good trajectory of Algorithm 3 reaching iterations `0, …, N` (`GoodTraj`, every solve satisfying (6),
the stopping rule failing at `0, …, N − 1`), under `Params`, on a graph without isolated nodes, with
`x_i = x^(S_i)`, `p_i = Dx_i`, `r_i = r(x_i)`, `p̃_i = Dx̃_i`, `r̃_i = r(x̃_i)` and `𝒯_i = S_{i+1} ∖ S_i`:
1. `N + 1 ≤ 1/λ`: no good run reaches more than `1/λ` iterations, so on `𝒢` the algorithm terminates after at
   most `1/λ` iterations;
2. for every `i ≤ N`: `x_i, p_i, r_i, x̃_i, p̃_i, r̃_i ≥ 0`, `x_i(v) > 0.9ακ` on `S_i`, and `vol(S_i) ≤ 1/λ`;
3. for every `i < N`: `x_{i+1} ≥ x_i` and (17);
4. if the stopping rule holds at `N` (the run returns `p̃ = Dx̃_N`), then `p̃ ≥ 0` and
   `0 ≤ r(D⁻¹p̃) ≤ (λ + η)d`.

**Formalization Note.** The probability clause `Pr{𝒢} ≥ 1 − δ` is the separate milestone
`LocalPush.lemma_5_3_prob`. The trivial branch `(λ + η)d(s) ≥ 1` (line 2) is excluded by `Params`. -/
theorem lemma_5_3 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : NoIsolated G) (s : V) (α lam η κ : ℝ) (hP : Params G s α lam η κ)
    (N : ℕ) (S : ℕ → Finset V) (xt : ℕ → V → ℝ) (hT : GoodTraj G s α lam η κ N S xt) :
    ((N : ℝ) + 1 ≤ 1 / lam) ∧
    (∀ i ≤ N,
      (∀ v, 0 ≤ exactX G s α lam S i v) ∧ (∀ v, 0 ≤ deg G v * exactX G s α lam S i v) ∧
      (∀ v, 0 ≤ exactR G s α lam S i v) ∧ (∀ v, 0 ≤ xt i v) ∧ (∀ v, 0 ≤ deg G v * xt i v) ∧
      (∀ v, 0 ≤ resid G α s (xt i) v) ∧
      (∀ v ∈ S i, 0.9 * α * κ < exactX G s α lam S i v) ∧ vol G (S i) ≤ 1 / lam) ∧
    (∀ i < N,
      (∀ v, exactX G s α lam S i v ≤ exactX G s α lam S (i + 1) v) ∧
      (∀ v ∈ S (i + 1) \ S i, (lam + 0.9 * κ) * deg G v < exactR G s α lam S i v) ∧
      (∀ v ∉ S (i + 1), exactR G s α lam S i v ≤ (lam + 1.1 * κ) * deg G v)) ∧
    (StopRule G s α lam η (S N) (xt N) →
      (∀ v, 0 ≤ deg G v * xt N v) ∧
      ∀ v, 0 ≤ resid G α s (fun u => deg G u * xt N u / deg G u) v ∧
        resid G α s (fun u => deg G u * xt N u / deg G u) v ≤ (lam + η) * deg G v) := by sorry

end LocalPush
