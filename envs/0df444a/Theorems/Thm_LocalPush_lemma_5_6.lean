-- Prove2me | Theorems.Thm_LocalPush_lemma_5_6
-- name    : LocalPush.lemma_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:07:48.164671+00:00
-- url     : https://prove2.me/theorems/0d0d037e-6c90-4d03-a9e9-2b353110f765
-- title:
--   Lemma 5.6 — interval identity (22) for $\Delta\psi(a,b)$
-- statement:
--   For every $0\le a<b\le K$,
--   $$\Delta\psi(a,b)=-\tfrac12\alpha\sum_{v\in V}\big(x_b(v)-x_a(v)\big)\big(r_b(v)-r_a(v)\big).\tag{22}$$
--
--   This expresses the decrease over a block of expansions through the endpoint states only.
--
--   Here $x_i=x^{(S_i)}$ and $r_i=r(x_i)$ are the exact states of a good trajectory with $K$ expansions, $\Delta x_i=x_{i+1}-x_i$, $\Delta r_i=r_{i+1}-r_i$, $\Delta\psi(a,b)=\psi_\lambda(x_a)-\psi_\lambda(x_b)$, $\Delta\psi_i=\Delta\psi(i,i+1)$ and $\mathcal T_i=S_{i+1}\setminus S_i$, under the parameters of Algorithm 3 with $(\lambda+\eta)d(s)<1$ on a graph without isolated nodes.
--
--   Differences from the source:
--   - generalization: the trajectory of a run of Algorithm 3 on the good event 𝒢 that performs K active-set expansions before terminating → every good trajectory GoodTraj … N S xt (every solve satisfies (6), the stopping rule fails at iterations 0, …, N − 1), terminated or not, with K = N; reason: the proof never uses termination; a terminated run on 𝒢 is a good trajectory with N = K, so the statement specializes to the source's
-- source:
--   Cui, Wei, Yang, Revisiting Local Push, STOC 2027 submission (manuscript sha256 4c36279a…), §5.2, Lemma 5.6, p.22 (PDF p.22)

import Mathlib
import Definitions.Def_LocalPush_GoodTraj

open Finset Matrix

namespace LocalPush

/-- **Lemma 5.6 (interval objective identity).**

Cui, Wei, Yang, *Revisiting Local Push: Faster Algorithms and Optimal Query Complexity for PageRank and
Effective Resistance*, STOC 2027 submission (manuscript sha256 4c36279a…), §5.2, Lemma 5.6, p.22 (PDF p.22).

"For every 0 ≤ a < b ≤ K, ∆ψ(a, b) = −½α ∑_{v∈V} (x_b(v) − x_a(v))(r_b(v) − r_a(v)). (22)" Here
∆ψ(a, b) := ψ_λ(x_a) − ψ_λ(x_b) (p.20).

**Formalization Note.** The paper states the lemma for a run that performs `K` expansions before terminating,
on the good event `𝒢`. Here it is stated for every good trajectory `GoodTraj … N S xt` (every solve satisfies (6),
no stop at iterations `0, …, N − 1`), terminated or not, with `K = N`; a terminated run on `𝒢` is one such
trajectory. `x_i = exactX … i = x^(S_i)`, `r_i = exactR … i = r(x_i)`, `∆ψ(a, b) = dPsi … a b`, and
`𝒯_i = S_{i+1} ∖ S_i`. -/
theorem lemma_5_6 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : NoIsolated G) (s : V) (α lam η κ : ℝ) (hP : Params G s α lam η κ)
    (N : ℕ) (S : ℕ → Finset V) (xt : ℕ → V → ℝ) (hT : GoodTraj G s α lam η κ N S xt) :
    ∀ a b : ℕ, a < b → b ≤ N →
      dPsi G s α lam S a b =
        -(1 / 2) * α * ∑ v, (exactX G s α lam S b v - exactX G s α lam S a v) *
          (exactR G s α lam S b v - exactR G s α lam S a v) := by sorry

end LocalPush
