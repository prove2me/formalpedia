-- Prove2me | Theorems.Thm_FracTruthSched_Supplement_theorem_4
-- name    : FracTruthSched.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T21:18:19.35954+00:00
-- url     : https://prove2.me/theorems/2539523b-4d58-4829-8319-52d49ea1fcaa
-- title:
--   Theorem 4 — expected makespan of Exp-Bounded-Square: $\mathbb E[\mathrm{Mech}_{\mathrm{EBS}}]\le\mathrm{Opt}\cdot((n+1)/2+q+2n^2e^{-q^2/(2n)})$
-- statement:
--   Let $t=(t_{ij})$ be any instance of $m\ge0$ tasks on $n\ge1$ unrelated machines with nonnegative processing times, and let $\mathrm{Opt}(t)$ be its optimal integral makespan. Exp-Bounded-Square (Algorithm 1) draws $E_{ij}\sim\mathrm{Exp}(1)$ for all $i,j$ and a uniform random permutation $\pi_j$ for every task $j$, all independent, and assigns each task $j$ within $N_j=\{i: t_{ij}\le 2\min_{i'}t_{i'j}\}$: to the first machine of $N_j$ in $\pi_j$ if $\min_{i'}t_{i'j}=0$, and otherwise to the minimizer of $E_{ij}t_{ij}^2$ over $N_j$, ties broken by $\pi_j$. Let $\mathrm{Mech}_{\mathrm{EBS}}(t)$ be the makespan of the resulting random allocation.
--
--   Then the makespan is integrable and, for every real $q\ge0$,
--   $$\mathbb E[\mathrm{Mech}_{\mathrm{EBS}}(t)]\ \le\ \mathrm{Opt}(t)\cdot\Big(\frac{n+1}{2}+q+2n^2\,e^{-q^2/(2n)}\Big).$$
--
--   With $q=2\sqrt{n\ln n}$ this gives the expected approximation ratio $(n+1)/2+O(\sqrt{n\ln n})$ of Corollary 3 for a universally truthful mechanism, matching the lower bound of Theorem 2 to first order.
--
--   Differences from the source:
--   - reading: e^{−q²/2n} (as printed in Theorem 4) → Real.exp (-(q^2) / (2 * n)), i.e. e^{−q²/(2n)}; reason: Lemma 9 and display (19) of the proof write e^{−q²/(2n)}, and Corollary 3 rewrites the term as 2e^{2 ln n − q²/(2n)}
--   - encoding: E[Mech_EBS(t)] over E_ij ∼ Exp(1) and independent uniform permutations π_j → ebsExpectedMakespan t: the average over all permutation tuples of the Bochner integral against the product Exp(1) law, together with the integrability of the makespan for every permutation tuple; reason: uniform independent permutations are the uniform law on the finite set of tuples, independent of E; stating integrability rules out the junk value 0 of a non-integrable Bochner integral, and the makespan is bounded and measurable so the clause is true
--   - encoding: every instance t (m tasks, n machines, nonnegative) → t : Fin n → Fin m → ℝ with Nonneg t, any m ≥ 0, [NeZero n]; reason: Lean indexing; Opt(t) = 0 is not excluded, as in the theorem
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, Theorem 4, p.21 (§4.3); Algorithm 1, p.19; Mech_EBS(t), p.20

import Mathlib
import Definitions.Def_FracTruthSched_Nonneg
import Definitions.Def_FracTruthSched_schedMakespan
import Definitions.Def_FracTruthSched_opt
import Definitions.Def_FracTruthSched_Supplement_ebsAssign
import Definitions.Def_FracTruthSched_Supplement_expWeightLaw
import Definitions.Def_FracTruthSched_Supplement_ebsExpectedMakespan

set_option autoImplicit false

namespace FracTruthSched.Supplement

open FracTruthSched MeasureTheory

/-- **Theorem 4** (Anastasiadis et al., arXiv:2611.06642v1, Theorem 4, p.21). For every instance `t`
and every `q ∈ ℝ≥0`, Exp-Bounded-Square computes a random allocation with an expected makespan of
`E[Mech_EBS(t)] ≤ Opt(t) · ((n + 1)/2 + q + 2n² · e^{−q²/(2n)})`, where `Opt(t)` is the optimal
(integral) makespan of instance `t`.

**Formalization Note.** Machines `Fin n` with `n ≥ 1` (`[NeZero n]`), tasks `Fin m` for any `m ≥ 0`;
the instance is nonnegative (§2.2, Algorithm 1's input). No `Opt(t) > 0` is assumed (the paper
assumes it only inside the proof, w.l.o.g.). The exponent is `−q²/(2n)`, as in Lemma 9 and display
(19) (the theorem prints `e^{−q²/2n}`). The conclusion first asserts that, for every choice of the
permutations, the makespan is integrable in the weights, so the expectation
`ebsExpectedMakespan t` is the genuine expected makespan of Algorithm 1 and not a junk value. -/
theorem theorem_4 {n m : ℕ} [NeZero n] (t : Fin n → Fin m → ℝ) (ht : Nonneg t)
    (q : ℝ) (hq : 0 ≤ q) :
    (∀ π : Fin m → Equiv.Perm (Fin n),
      Integrable (fun E => schedMakespan t (ebsAssign t E π)) (expWeightLaw n m)) ∧
    ebsExpectedMakespan t ≤
      opt t * (((n : ℝ) + 1) / 2 + q + 2 * (n : ℝ) ^ 2 * Real.exp (-(q ^ 2) / (2 * (n : ℝ)))) := by sorry

end FracTruthSched.Supplement
