-- Prove2me | Theorems.Thm_FracTruthSched_star_bound
-- name    : FracTruthSched.star_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:34:00.232412+00:00
-- url     : https://prove2.me/theorems/259616a1-fd27-47c8-b777-e1505edd1121
-- title:
--   Star bound — $\rho(1+\varepsilon)\ge\rho\lambda\ge1+\frac{c(n-1)}2(1-\frac1\ell)^{n-2}$
-- statement:
--   Let $n\ge2$, $\ell\ge2$, $\rho\in\mathbb R$, and let $(x,P)$ be a feasible truthful mechanism on the graph inputs of $MC_\ell$ with properties (i)–(iv) of Lemma 1 and the load bound $\mathrm{Mech}_x(t)\le\rho\,C(t)$ at every graph input (7). Then for every rational $0<c<1$ and every $\varepsilon>0$ there is a common leaf value $\lambda\in(1,1+\varepsilon)$ with
--   $$\rho(1+\varepsilon)\ \ge\ \rho\lambda\ \ge\ 1+\frac{c(n-1)}{2}\Big(1-\frac1\ell\Big)^{n-2}.$$
--
--   This is the bound the star argument of §3.3.3–3.4 gives at the input $I^*$: the root keeps about half of a star of $n-1$ tasks of value $c$ and processes its unit self-loop, while $C(I^*)\le\lambda$. Letting $\ell\to\infty$, $c\uparrow1$ and $\varepsilon\downarrow0$ gives $\rho\ge(n+1)/2$.
--
--   Differences from the source:
--   - generalization: a limit mechanism on MC_ℓ (Definition 6: the mechanism constructed in Lemma 1) → every feasible truthful mechanism on the graph inputs of MC_ℓ with properties (i)–(iv) of Lemma 1 and the load bound (7) with constant ρ; reason: the argument of §3.3.3–3.4 uses exactly these properties (Lemmas 3, 4, 5, 2 (b), eligibility, WMON, (7)); every limit mechanism has these properties by Lemma 1, so the statement specializes to the source's
--   - encoding: the display for the λ chosen by Lemma 5 → there exists λ ∈ (1, 1+ε) satisfying both inequalities of the display; reason: λ is the value Lemma 5 provides; the display is asserted for it
--   - encoding: a graph input of MC_ℓ: the two endpoint values of every edge and the owner value of every self-loop, all nonnegative, and no other values → t : Fin n → CoreTask n ℓ → ℝ, nonnegative and 0 at every (machine, task) pair that is not incident (IsGraphInput); edges of Q{u,v} are encoded with u < v; reason: a machine's cost Σ_e t_ie x_ie is then its cost on its incident tasks; same inputs and same costs
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, §3.4, proof of Theorem 2, first display, p.18 (with (14)–(16), pp.15–16)

import Mathlib
import Definitions.Def_FracTruthSched_IsFeasibleOn
import Definitions.Def_FracTruthSched_IsTruthfulOn
import Definitions.Def_FracTruthSched_makespan
import Definitions.Def_FracTruthSched_IsGraphInput
import Definitions.Def_FracTruthSched_C
import Definitions.Def_FracTruthSched_IsEligible
import Definitions.Def_FracTruthSched_HasUniqueZeros
import Definitions.Def_FracTruthSched_HasZeroTypeIrrelevance
import Definitions.Def_FracTruthSched_IsClassSymmetric

set_option autoImplicit false

namespace FracTruthSched

/-- **Star bound** (Anastasiadis et al., arXiv:2611.06642v1, §3.4, proof of Theorem 2, first display,
p.18). For `n ≥ 2`, the construction of §3.3.3–3.4 and the load bound (7) give, for every `ℓ ≥ 2`,
rational `0 < c < 1` and `ε > 0`,
`ρ(1 + ε) ≥ ρλ ≥ 1 + (c(n − 1)/2)(1 − 1/ℓ)^{n−2}`,
where `λ ∈ (1, 1 + ε)` is the common leaf value of Lemma 5.

**Formalization Note.** Stated for every feasible truthful mechanism on `MC_ℓ` with properties
(i)–(iv) of Lemma 1 and the bound (7) with constant `ρ` (every limit mechanism has them). The
conclusion asserts a `λ ∈ (1, 1 + ε)` with both inequalities of the display. `c` is rational, as
printed; `(n − 1)/2` and `1 − 1/ℓ` are real numbers, and the exponent `n − 2` is a natural number
with `n ≥ 2`. -/
theorem star_bound {n ℓ : ℕ} [NeZero n] (hn : 2 ≤ n) (hℓ : 2 ≤ ℓ) (ρ : ℝ)
    (M : FracMech n (CoreTask n ℓ))
    (hfeas : IsFeasibleOn IsGraphInput M) (htruth : IsTruthfulOn IsGraphInput M)
    (hel : IsEligible M) (huz : HasUniqueZeros M) (hzti : HasZeroTypeIrrelevance M)
    (hsym : IsClassSymmetric M) (hload : ∀ t, IsGraphInput t → makespan M t ≤ ρ * C t)
    (c : ℚ) (hc0 : 0 < c) (hc1 : c < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ lam ∈ Set.Ioo 1 (1 + ε),
      1 + (c : ℝ) * ((n : ℝ) - 1) / 2 * (1 - 1 / (ℓ : ℝ)) ^ (n - 2) ≤ ρ * lam ∧
        ρ * lam ≤ ρ * (1 + ε) := by sorry

end FracTruthSched
