-- Prove2me | Theorems.Thm_LocalPush_lemma_5_9
-- name    : LocalPush.lemma_5_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:07:46.722291+00:00
-- url     : https://prove2.me/theorems/011574dd-252e-4242-877d-176727154749
-- title:
--   Lemma 5.9 — the number of expansions satisfies $K<\lceil2/\sqrt\alpha\rceil(2+\log_4(10/(\alpha\eta^2)))$
-- statement:
--   The number $K$ of active-set expansions satisfies
--   $$K\ <\ \Big\lceil\frac{2}{\sqrt\alpha}\Big\rceil\Big(2+\log_4\frac{10}{\alpha\eta^2}\Big).$$
--
--   This is the $O\big(\frac1{\sqrt\alpha}\log\frac1{\alpha\eta}\big)$ bound on the number of SDD solves behind the $1/\sqrt\alpha$ factor in Theorem 1.2.
--
--   Here $x_i=x^{(S_i)}$ and $r_i=r(x_i)$ are the exact states of a good trajectory with $K$ expansions, $\Delta x_i=x_{i+1}-x_i$, $\Delta r_i=r_{i+1}-r_i$, $\Delta\psi(a,b)=\psi_\lambda(x_a)-\psi_\lambda(x_b)$, $\Delta\psi_i=\Delta\psi(i,i+1)$ and $\mathcal T_i=S_{i+1}\setminus S_i$, under the parameters of Algorithm 3 with $(\lambda+\eta)d(s)<1$ on a graph without isolated nodes.
--
--   Differences from the source:
--   - generalization: the trajectory of a run of Algorithm 3 on the good event 𝒢 that performs K active-set expansions before terminating → every good trajectory GoodTraj … N S xt (every solve satisfies (6), the stopping rule fails at iterations 0, …, N − 1), terminated or not, with K = N; reason: the proof never uses termination; a terminated run on 𝒢 is a good trajectory with N = K, so the statement specializes to the source's
--   - reading: K < ⌈2/√α⌉(2 + log₄(10/(αη²))) = O((1/√α) log(1/(αη))) → the explicit bound K < ⌈2/√α⌉(2 + log₄(10/(αη²))); reason: the trailing = O(·) restates the explicit bound asymptotically and follows from it; it is not a separate claim about K
-- source:
--   Cui, Wei, Yang, Revisiting Local Push, STOC 2027 submission (manuscript sha256 4c36279a…), §5.2, Lemma 5.9, p.25 (PDF p.25)

import Mathlib
import Definitions.Def_LocalPush_GoodTraj

open Finset Matrix

namespace LocalPush

/-- **Lemma 5.9 (the number of active-set expansions).**

Cui, Wei, Yang, *Revisiting Local Push: Faster Algorithms and Optimal Query Complexity for PageRank and
Effective Resistance*, STOC 2027 submission (manuscript sha256 4c36279a…), §5.2, Lemma 5.9, p.25 (PDF p.25).

"On the event 𝒢, the number K of active-set expansions performed by Algorithm 3 satisfies
K < ⌈2/√α⌉(2 + log₄(10/(αη²))) = O((1/√α) log(1/(αη)))."

**Formalization Note.** The paper states the lemma for a run that performs `K` expansions before terminating,
on the good event `𝒢`. Here it is stated for every good trajectory `GoodTraj … N S xt` (every solve satisfies (6),
no stop at iterations `0, …, N − 1`), terminated or not, with `K = N`; a terminated run on `𝒢` is one such
trajectory. `x_i = exactX … i = x^(S_i)`, `r_i = exactR … i = r(x_i)`, `∆ψ(a, b) = dPsi … a b`, and
`𝒯_i = S_{i+1} ∖ S_i`. The trailing `= O(·)` is a remark of the page and is not part of the statement. -/
theorem lemma_5_9 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : NoIsolated G) (s : V) (α lam η κ : ℝ) (hP : Params G s α lam η κ)
    (N : ℕ) (S : ℕ → Finset V) (xt : ℕ → V → ℝ) (hT : GoodTraj G s α lam η κ N S xt) :
    (N : ℝ) < (⌈2 / Real.sqrt α⌉₊ : ℝ) * (2 + Real.logb 4 (10 / (α * η ^ 2))) := by sorry

end LocalPush
