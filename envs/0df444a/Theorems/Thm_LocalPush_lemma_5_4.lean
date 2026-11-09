-- Prove2me | Theorems.Thm_LocalPush_lemma_5_4
-- name    : LocalPush.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:07:34.572972+00:00
-- url     : https://prove2.me/theorems/c3091b74-cac8-4ac8-bf42-9079b7143d76
-- title:
--   Lemma 5.4 — one-step identity (19) and lower bound (20) for $\Delta\psi_i$
-- statement:
--   For every $0\le i<K$,
--   $$\Delta\psi_i=-\tfrac12\alpha\sum_{v\in V}\Delta x_i(v)\,\Delta r_i(v)=\tfrac12\Delta x_i^\top L_\alpha\Delta x_i\tag{19}$$
--   and
--   $$\Delta\psi_i\ \ge\ \tfrac12\alpha^2\sum_{v\in\mathcal T_i}\frac{\Delta r_i(v)^2}{d(v)}.\tag{20}$$
--
--   Each expansion therefore decreases the potential by an amount controlled by the residue drop on the newly activated nodes.
--
--   Here $x_i=x^{(S_i)}$ and $r_i=r(x_i)$ are the exact states of a good trajectory with $K$ expansions, $\Delta x_i=x_{i+1}-x_i$, $\Delta r_i=r_{i+1}-r_i$, $\Delta\psi(a,b)=\psi_\lambda(x_a)-\psi_\lambda(x_b)$, $\Delta\psi_i=\Delta\psi(i,i+1)$ and $\mathcal T_i=S_{i+1}\setminus S_i$, under the parameters of Algorithm 3 with $(\lambda+\eta)d(s)<1$ on a graph without isolated nodes.
--
--   Differences from the source:
--   - generalization: the trajectory of a run of Algorithm 3 on the good event 𝒢 that performs K active-set expansions before terminating → every good trajectory GoodTraj … N S xt (every solve satisfies (6), the stopping rule fails at iterations 0, …, N − 1), terminated or not, with K = N; reason: the proof never uses termination; a terminated run on 𝒢 is a good trajectory with N = K, so the statement specializes to the source's
-- source:
--   Cui, Wei, Yang, Revisiting Local Push, STOC 2027 submission (manuscript sha256 4c36279a…), §5.2, Lemma 5.4, p.20 (PDF p.20)

import Mathlib
import Definitions.Def_LocalPush_GoodTraj

open Finset Matrix

namespace LocalPush

/-- **Lemma 5.4 (one-step objective identity and lower bound).**

Cui, Wei, Yang, *Revisiting Local Push: Faster Algorithms and Optimal Query Complexity for PageRank and
Effective Resistance*, STOC 2027 submission (manuscript sha256 4c36279a…), §5.2, Lemma 5.4, p.20 (PDF p.20).

"For every 0 ≤ i < K, we have ∆ψ_i = −½α ∑_{v∈V} ∆x_i(v)∆r_i(v) = ½∆x_iᵀL_α∆x_i (19) and
∆ψ_i ≥ ½α² ∑_{v∈𝒯_i} ∆r_i(v)²/d(v). (20)" Here ∆x_i := x_{i+1} − x_i, ∆r_i := r_{i+1} − r_i, and
∆ψ_i := ψ_λ(x_i) − ψ_λ(x_{i+1}) (p.20).

**Formalization Note.** The paper states the lemma for a run that performs `K` expansions before terminating,
on the good event `𝒢`. Here it is stated for every good trajectory `GoodTraj … N S xt` (every solve satisfies (6),
no stop at iterations `0, …, N − 1`), terminated or not, with `K = N`; a terminated run on `𝒢` is one such
trajectory. `x_i = exactX … i = x^(S_i)`, `r_i = exactR … i = r(x_i)`, `∆ψ(a, b) = dPsi … a b`, and
`𝒯_i = S_{i+1} ∖ S_i`. -/
theorem lemma_5_4 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : NoIsolated G) (s : V) (α lam η κ : ℝ) (hP : Params G s α lam η κ)
    (N : ℕ) (S : ℕ → Finset V) (xt : ℕ → V → ℝ) (hT : GoodTraj G s α lam η κ N S xt) :
    ∀ i < N,
      dPsi G s α lam S i (i + 1) =
          -(1 / 2) * α * ∑ v, (exactX G s α lam S (i + 1) v - exactX G s α lam S i v) *
            (exactR G s α lam S (i + 1) v - exactR G s α lam S i v) ∧
        -(1 / 2) * α * ∑ v, (exactX G s α lam S (i + 1) v - exactX G s α lam S i v) *
            (exactR G s α lam S (i + 1) v - exactR G s α lam S i v) =
          (1 / 2) * ((exactX G s α lam S (i + 1) - exactX G s α lam S i) ⬝ᵥ
            (Lα G α *ᵥ (exactX G s α lam S (i + 1) - exactX G s α lam S i))) ∧
        (1 / 2) * α ^ 2 * ∑ v ∈ S (i + 1) \ S i,
            (exactR G s α lam S (i + 1) v - exactR G s α lam S i v) ^ 2 / deg G v ≤
          dPsi G s α lam S i (i + 1) := by sorry

end LocalPush
