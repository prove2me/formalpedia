-- Prove2me | Theorems.Thm_IntMul_Kappa_moment_recurrence_bound
-- name    : IntMul.Kappa.moment_recurrence_bound
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T20:23:09.111512+00:00
-- url     : https://prove2.me/theorems/0c6de9e0-34a0-449d-b782-7b5fcbcc48cd
-- title:
--   Moment inequality implies a power-saving recursive cost
-- statement:
--   **Moment inequality implies a power-saving cost.** Let $m\ge2$ and $W\ge1$ be integers, and let $h$ be a child-width histogram: a finite list of pairs $(w,n_w)$ with $0<w<m$. Let $0<\tau\le1$ and suppose the moment inequality
--   $$\sum_{(w,n_w)\in h} n_w\Big(\frac wm\Big)^{\tau}<W$$
--   holds. Let $c:\mathbb N\to\mathbb R$ be nondecreasing and satisfy, for a constant $K$ and every $f\ge1$,
--   $$c(mf)\le\frac1W\sum_{(w,n_w)\in h} n_w\,c(wf)+K.$$
--   Then there is a constant $A$ with $c(x)\le A\,x^{\tau}$ for every $x\ge1$.
--
--   This is the recursive saving of the OpenAI manuscript in histogram form: a network on $W$ roles of full width $m$ makes $n_w$ child calls of width $w$ on streams of volume $V/W$, so the normalised cost $c$ of a call obeys the displayed recursion, and the strict moment inequality ($s<Wm$ in the uniform case) yields cost exponent $\tau=1-a<1$. It is the analytic step behind every moment certificate of the $\kappa$-improvement rounds.
--
--   **Formalization Note** The moment is `histMoment` from `IntMul_KappaFramework`. The recursion is required only at multiples $mf$; monotonicity of $c$ covers the other arguments.
-- source:
--   OpenAI, Integer multiplication below n log n, preprint, 23 September 2026, https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §1 'Linear networks and the recursive saving' (s < Wm gives the power saving); histogram moment form: S. Jain, integer-mult-kappa, scripts/certificate_round8.py and lean/Round8.lean (momentOK)

import Definitions.Def_IntMul_KappaFramework

namespace IntMul.Kappa

theorem moment_recurrence_bound (h : List (ℕ × ℕ)) (m W : ℕ) (τ K : ℝ) (c : ℕ → ℝ)
    (hm : 2 ≤ m) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    (hw : ∀ p ∈ h, 0 < p.1 ∧ p.1 < m) (hW : 0 < W)
    (hmom : histMoment h m τ < W) (hmono : Monotone c)
    (hrec : ∀ f : ℕ, 1 ≤ f →
      c (m * f) ≤ (h.map fun p => (p.2 : ℝ) * c (p.1 * f)).sum / W + K) :
    ∃ A : ℝ, ∀ x : ℕ, 1 ≤ x → c x ≤ A * (x : ℝ) ^ τ := by sorry

end IntMul.Kappa
