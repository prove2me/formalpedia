-- Prove2me | Theorems.Thm_LocalPush_lemma_5_7
-- name    : LocalPush.lemma_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:07:58.768405+00:00
-- url     : https://prove2.me/theorems/537e772c-1169-4c49-8551-5f0d096bf983
-- title:
--   Lemma 5.7 — adjacent blocks: $\Delta\psi(a,a+L)\le\frac1{\alpha L^2}\Delta\psi(a-L,a)+1.1\alpha\kappa$
-- statement:
--   For all integers $a$ and $L$ with $a\ge L\ge1$ and $a+L\le K$,
--   $$\Delta\psi(a,a+L)\ \le\ \frac{1}{\alpha L^2}\,\Delta\psi(a-L,a)+1.1\alpha\kappa.$$
--
--   With $L=\lceil2/\sqrt\alpha\rceil$ the potential decrease contracts by a factor $4$ from one block to the next, which is the source of the $1/\sqrt\alpha$ dependence.
--
--   Here $x_i=x^{(S_i)}$ and $r_i=r(x_i)$ are the exact states of a good trajectory with $K$ expansions, $\Delta x_i=x_{i+1}-x_i$, $\Delta r_i=r_{i+1}-r_i$, $\Delta\psi(a,b)=\psi_\lambda(x_a)-\psi_\lambda(x_b)$, $\Delta\psi_i=\Delta\psi(i,i+1)$ and $\mathcal T_i=S_{i+1}\setminus S_i$, under the parameters of Algorithm 3 with $(\lambda+\eta)d(s)<1$ on a graph without isolated nodes.
--
--   Differences from the source:
--   - generalization: the trajectory of a run of Algorithm 3 on the good event 𝒢 that performs K active-set expansions before terminating → every good trajectory GoodTraj … N S xt (every solve satisfies (6), the stopping rule fails at iterations 0, …, N − 1), terminated or not, with K = N; reason: the proof never uses termination; a terminated run on 𝒢 is a good trajectory with N = K, so the statement specializes to the source's
-- source:
--   Cui, Wei, Yang, Revisiting Local Push, STOC 2027 submission (manuscript sha256 4c36279a…), §5.2, Lemma 5.7, p.22 (PDF p.22)

import Mathlib
import Definitions.Def_LocalPush_GoodTraj

open Finset Matrix

namespace LocalPush

/-- **Lemma 5.7 (comparison of adjacent blocks of expansions).**

Cui, Wei, Yang, *Revisiting Local Push: Faster Algorithms and Optimal Query Complexity for PageRank and
Effective Resistance*, STOC 2027 submission (manuscript sha256 4c36279a…), §5.2, Lemma 5.7, p.22 (PDF p.22).

"For any integers a and L such that a ≥ L ≥ 1 and a + L ≤ K, ∆ψ(a, a + L) ≤ (1/(αL²))∆ψ(a − L, a) + 1.1ακ."

**Formalization Note.** The paper states the lemma for a run that performs `K` expansions before terminating,
on the good event `𝒢`. Here it is stated for every good trajectory `GoodTraj … N S xt` (every solve satisfies (6),
no stop at iterations `0, …, N − 1`), terminated or not, with `K = N`; a terminated run on `𝒢` is one such
trajectory. `x_i = exactX … i = x^(S_i)`, `r_i = exactR … i = r(x_i)`, `∆ψ(a, b) = dPsi … a b`, and
`𝒯_i = S_{i+1} ∖ S_i`. Since `a ≥ L ≥ 1`, both are natural numbers. -/
theorem lemma_5_7 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : NoIsolated G) (s : V) (α lam η κ : ℝ) (hP : Params G s α lam η κ)
    (N : ℕ) (S : ℕ → Finset V) (xt : ℕ → V → ℝ) (hT : GoodTraj G s α lam η κ N S xt) :
    ∀ a L : ℕ, L ≤ a → 1 ≤ L → a + L ≤ N →
      dPsi G s α lam S a (a + L) ≤
        1 / (α * (L : ℝ) ^ 2) * dPsi G s α lam S (a - L) a + 1.1 * α * κ := by sorry

end LocalPush
