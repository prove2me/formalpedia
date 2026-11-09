-- Prove2me | Theorems.Thm_LocalPush_lemma_5_8
-- name    : LocalPush.lemma_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:08:01.432624+00:00
-- url     : https://prove2.me/theorems/9c94ed66-d363-4a71-9862-dde1c6ffc524
-- title:
--   Lemma 5.8 — $\Delta\psi(0,b)\le\frac12\alpha$ (26) and $\Delta\psi_i>0.4\alpha^2\eta^2$ (27)
-- statement:
--   For every $1\le b\le K$,
--   $$\Delta\psi(0,b)\le\tfrac12\alpha,\tag{26}$$
--   and for every $0\le i<K$,
--   $$\Delta\psi_i>0.4\alpha^2\eta^2.\tag{27}$$
--
--   The total decrease is bounded and every expansion decreases the potential by a definite amount; together with Lemma 5.7 this bounds the number of expansions.
--
--   Here $x_i=x^{(S_i)}$ and $r_i=r(x_i)$ are the exact states of a good trajectory with $K$ expansions, $\Delta x_i=x_{i+1}-x_i$, $\Delta r_i=r_{i+1}-r_i$, $\Delta\psi(a,b)=\psi_\lambda(x_a)-\psi_\lambda(x_b)$, $\Delta\psi_i=\Delta\psi(i,i+1)$ and $\mathcal T_i=S_{i+1}\setminus S_i$, under the parameters of Algorithm 3 with $(\lambda+\eta)d(s)<1$ on a graph without isolated nodes.
--
--   Differences from the source:
--   - generalization: the trajectory of a run of Algorithm 3 on the good event 𝒢 that performs K active-set expansions before terminating → every good trajectory GoodTraj … N S xt (every solve satisfies (6), the stopping rule fails at iterations 0, …, N − 1), terminated or not, with K = N; reason: the proof never uses termination; a terminated run on 𝒢 is a good trajectory with N = K, so the statement specializes to the source's
-- source:
--   Cui, Wei, Yang, Revisiting Local Push, STOC 2027 submission (manuscript sha256 4c36279a…), §5.2, Lemma 5.8, p.25 (PDF p.25)

import Mathlib
import Definitions.Def_LocalPush_GoodTraj

open Finset Matrix

namespace LocalPush

/-- **Lemma 5.8 (bounds on the objective decrease).**

Cui, Wei, Yang, *Revisiting Local Push: Faster Algorithms and Optimal Query Complexity for PageRank and
Effective Resistance*, STOC 2027 submission (manuscript sha256 4c36279a…), §5.2, Lemma 5.8, p.25 (PDF p.25).

"For every 1 ≤ b ≤ K, ∆ψ(0, b) ≤ ½α. (26) Moreover, for every 0 ≤ i < K, it holds that ∆ψ_i > 0.4α²η². (27)"

**Formalization Note.** The paper states the lemma for a run that performs `K` expansions before terminating,
on the good event `𝒢`. Here it is stated for every good trajectory `GoodTraj … N S xt` (every solve satisfies (6),
no stop at iterations `0, …, N − 1`), terminated or not, with `K = N`; a terminated run on `𝒢` is one such
trajectory. `x_i = exactX … i = x^(S_i)`, `r_i = exactR … i = r(x_i)`, `∆ψ(a, b) = dPsi … a b`, and
`𝒯_i = S_{i+1} ∖ S_i`. -/
theorem lemma_5_8 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : NoIsolated G) (s : V) (α lam η κ : ℝ) (hP : Params G s α lam η κ)
    (N : ℕ) (S : ℕ → Finset V) (xt : ℕ → V → ℝ) (hT : GoodTraj G s α lam η κ N S xt) :
    (∀ b : ℕ, 1 ≤ b → b ≤ N → dPsi G s α lam S 0 b ≤ (1 / 2) * α) ∧
      ∀ i < N, 0.4 * α ^ 2 * η ^ 2 < dPsi G s α lam S i (i + 1) := by sorry

end LocalPush
