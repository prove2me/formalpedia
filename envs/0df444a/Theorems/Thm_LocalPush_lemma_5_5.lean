-- Prove2me | Theorems.Thm_LocalPush_lemma_5_5
-- name    : LocalPush.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:07:51.302224+00:00
-- url     : https://prove2.me/theorems/518a7345-9e4a-4a78-b328-26054683facb
-- title:
--   Lemma 5.5 — orthogonality $\sum_v\Delta x_i(v)\Delta r_j(v)=0$ for $i\neq j$
-- statement:
--   For all $0\le i,j<K$ with $i\neq j$,
--   $$\sum_{v\in V}\Delta x_i(v)\,\Delta r_j(v)=0.$$
--
--   The orthogonality removes all cross terms when one-step decreases are summed over an interval.
--
--   Here $x_i=x^{(S_i)}$ and $r_i=r(x_i)$ are the exact states of a good trajectory with $K$ expansions, $\Delta x_i=x_{i+1}-x_i$, $\Delta r_i=r_{i+1}-r_i$, $\Delta\psi(a,b)=\psi_\lambda(x_a)-\psi_\lambda(x_b)$, $\Delta\psi_i=\Delta\psi(i,i+1)$ and $\mathcal T_i=S_{i+1}\setminus S_i$, under the parameters of Algorithm 3 with $(\lambda+\eta)d(s)<1$ on a graph without isolated nodes.
--
--   Differences from the source:
--   - generalization: the trajectory of a run of Algorithm 3 on the good event 𝒢 that performs K active-set expansions before terminating → every good trajectory GoodTraj … N S xt (every solve satisfies (6), the stopping rule fails at iterations 0, …, N − 1), terminated or not, with K = N; reason: the proof never uses termination; a terminated run on 𝒢 is a good trajectory with N = K, so the statement specializes to the source's
-- source:
--   Cui, Wei, Yang, Revisiting Local Push, STOC 2027 submission (manuscript sha256 4c36279a…), §5.2, Lemma 5.5, p.21 (PDF p.21)

import Mathlib
import Definitions.Def_LocalPush_GoodTraj

open Finset Matrix

namespace LocalPush

/-- **Lemma 5.5 (orthogonality of increments).**

Cui, Wei, Yang, *Revisiting Local Push: Faster Algorithms and Optimal Query Complexity for PageRank and
Effective Resistance*, STOC 2027 submission (manuscript sha256 4c36279a…), §5.2, Lemma 5.5, p.21 (PDF p.21).

"For any i ≠ j, ∑_{v∈V} ∆x_i(v)∆r_j(v) = 0." Here ∆x_i := x_{i+1} − x_i and ∆r_j := r_{j+1} − r_j for
0 ≤ i, j < K (p.20).

**Formalization Note.** The paper states the lemma for a run that performs `K` expansions before terminating,
on the good event `𝒢`. Here it is stated for every good trajectory `GoodTraj … N S xt` (every solve satisfies (6),
no stop at iterations `0, …, N − 1`), terminated or not, with `K = N`; a terminated run on `𝒢` is one such
trajectory. `x_i = exactX … i = x^(S_i)`, `r_i = exactR … i = r(x_i)`, `∆ψ(a, b) = dPsi … a b`, and
`𝒯_i = S_{i+1} ∖ S_i`. -/
theorem lemma_5_5 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : NoIsolated G) (s : V) (α lam η κ : ℝ) (hP : Params G s α lam η κ)
    (N : ℕ) (S : ℕ → Finset V) (xt : ℕ → V → ℝ) (hT : GoodTraj G s α lam η κ N S xt) :
    ∀ i < N, ∀ j < N, i ≠ j →
      ∑ v, (exactX G s α lam S (i + 1) v - exactX G s α lam S i v) *
        (exactR G s α lam S (j + 1) v - exactR G s α lam S j v) = 0 := by sorry

end LocalPush
