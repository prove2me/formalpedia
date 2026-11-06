-- Prove2me | Theorems.Thm_OrderedExperts_theorem_2
-- name    : OrderedExperts.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:39:02.972081+00:00
-- url     : https://prove2.me/theorems/bc8b78dc-a8ce-48b5-9d5f-f3ac9fc3c1b9
-- title:
--   Theorem 2 — separated two-point upper bound $O(\log(|\mathcal F|T)\sqrt{T\log|\mathcal F|})$
-- statement:
--   Fix a horizon $T\ge2$, a totally ordered action space $(\mathcal A,\preceq)$ with least element $\bot$ and greatest element $\top$, and a class $\mathcal F$ of $|\mathcal F|\ge2$ experts. An oblivious adversary fixes in advance the recommendations $a_{t,f}\in\mathcal A$ and, for every round, a loss of the separated monotone problem $\ell_t=\ell^\uparrow_t+\ell^\downarrow_t$ ($\ell^\uparrow_t$ nondecreasing in $[0,1/2]$ with $\ell^\uparrow_t(\bot)=0$, $\ell^\downarrow_t$ nonincreasing in $[0,1/2]$ with $\ell^\downarrow_t(\top)=0$). The learner runs Algorithm 2 — exponential weights over experts, smoothed onto the active chain with $\xi=1/T$, the reversible pair sampler, and the forward and backward endpoint flow estimates — paying $\frac12(\ell_t(x_{t,A_t})+\ell_t(x_{t,B_t}))$ per round.
--
--   There are an absolute constant $C>0$ and a learning-rate rule $\eta=\eta(|\mathcal F|,T)>0$ such that, for every such instance and arbitrary recommendations,
--   $$
--   \mathbb E\,\mathrm{Reg}_T(\mathcal F)=\mathbb E\sum_{t=1}^T\frac{\ell_t(x_{t,A_t})+\ell_t(x_{t,B_t})}{2}-\min_{f\in\mathcal F}\sum_{t=1}^T\ell_t(a_{t,f})\le C\log(|\mathcal F|T)\sqrt{T\log|\mathcal F|}.
--   $$
--
--   This is the paper's main upper bound for the separated monotone problem; it matches the $\Omega(\sqrt T\log\min\{|\mathcal F|,\sqrt T\})$ lower bound of Theorem 3 up to logarithmic factors.
--
--   **Formalization Note** The expectation is computed exactly by the finite recursion over the pairs drawn each round (`expPaid`); experts are $\mathrm{Fin}\,n$ with $n=|\mathcal F|$; rounds are $0,\dots,T-1$; the action space is any type with a linear order and top and bottom elements.
--
--   Differences from the source:
--   - reading: Algorithm 2 with a suitable learning rate; $O(\cdot)$ → an absolute constant $C$ and a rule $\eta(|\mathcal F|,T)>0$, both chosen before the action space and the instance; reason: the proof (B.2) tunes $\eta$ using only $|\mathcal F|$ and $T$ (via $\Lambda_t\le1+\log(|\mathcal F|T)$); this is the stronger reading
--   - encoding: $\min_{f\in\mathcal F}$ in the regret → the bound against every expert $f$; reason: equivalent: the bound for every $f$ is the bound for the minimizer
--   - encoding: expectation over learner randomness → the exact finite recursion `expPaid` over the pair law $\pi_t(a)\kappa_t(a,b)$ of each round; reason: oblivious adversary; the pairs are the only randomness; same quantity
--   - encoding: experts $\mathcal F$, rounds $1,\dots,T$ → `Fin n` with $n=|\mathcal F|$, rounds $0,\dots,T-1$; reason: Lean convention; same instances
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version, sha256 a6480b1e…fe429), Theorem 2, p.11; Algorithm 2, p.11; Sec. 2, pp.4–6; Appendix B.2, pp.20–21

import Definitions.Def_OrderedExperts_expPaid
import Definitions.Def_OrderedExperts_IsSepMonoLoss
open Finset

namespace OrderedExperts

/-- **Theorem 2 (Separated two-point upper bound).** Zuo, *Online Learning with Ordered Experts (via Two-point Feedback)*, STOC 2027 submission (held version), Theorem 2, p.11:
"For every oblivious loss sequence of the separated monotone problem and arbitrary current
recommendations, Algorithm 2 with a suitable learning rate satisfies
`ERegT(F) = O(log(|F|T) √(T log|F|))`." The model is that of Sec. 2 (pp.4–6): `T ≥ 2`, a totally
ordered action space with `⊥` and `⊤`, `|F| ≥ 2` experts, and
`RegT(F) = Σ_t ½(ℓt(At) + ℓt(Bt)) − min_f Σ_t ℓt(at,f)`.

There are an absolute constant `C > 0` and a learning-rate rule `η(n, T) > 0` such that for every
totally ordered action space `A` with least and greatest elements, every `n ≥ 2`, `T ≥ 2`, every
recommendation sequence `rec` and every separated monotone loss sequence `(up, down)`, the expected
cumulative paid loss of Algorithm 2 run with `η(n, T)` exceeds the cumulative loss of every expert `f`
by at most `C log(nT) √(T log n)`.

**Formalization Note.** The expectation is the exact finite recursion `expPaid` over the pair drawn
each round; the bound against every expert `f` is the bound against the minimum. `|F| = n`
(`Fin n`); rounds are `0, …, T−1`; `C` and the rule `η` are chosen before the action space and the
instance. -/
theorem theorem_2.{u} :
    ∃ C : ℝ, 0 < C ∧ ∃ η : ℕ → ℕ → ℝ, (∀ n T, 0 < η n T) ∧
      ∀ (A : Type u) [LinearOrder A] [BoundedOrder A] (n T : ℕ), 2 ≤ n → 2 ≤ T →
      ∀ (rec : ℕ → Fin n → A) (up down : ℕ → A → ℝ),
        (∀ t < T, IsSepMonoLoss (up t) (down t)) →
        ∀ f : Fin n,
          expPaid (η n T) T rec up down T 0 (fun _ _ => 0) -
              ∑ t ∈ range T, (up t (rec t f) + down t (rec t f)) ≤
            C * Real.log ((n : ℝ) * T) * Real.sqrt ((T : ℝ) * Real.log n) := by sorry

end OrderedExperts
