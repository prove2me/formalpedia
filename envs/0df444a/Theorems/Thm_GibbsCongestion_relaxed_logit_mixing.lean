-- Prove2me | Theorems.Thm_GibbsCongestion_relaxed_logit_mixing
-- name    : GibbsCongestion.relaxed_logit_mixing
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:04:35.990014+00:00
-- url     : https://prove2.me/theorems/b3338bb9-1c93-463f-9002-fecab0178047
-- title:
--   Theorem 4.4: relaxed logit dynamics in EP congestion games mix in $n^3(\log(n\log|\mathcal P|+T\Phi_{\max})+\log\frac{1}{2\epsilon^2})$ steps (corrected: RHS; rounded up at $n=1$)
-- statement:
--   Let $\Gamma$ be an extension parallel congestion game with common strategy set $\mathcal P$ (the $o,d$-paths of an EP network), $n\ge1$ players and non-negative, non-decreasing cost functions, and let $T\ge0$ and $\epsilon>0$. Let $P$ be the relaxed logit dynamics at temperature $T$ (with probability $\tfrac12$ two random distinct players swap their strategies, with probability $\tfrac12$ a logit step), $\pi$ the Gibbs distribution $\pi(s)\propto e^{-T\Phi(s)}$, and
--   $$\Phi_{\max}=\max_{r\in\mathcal P^n}\Phi(r).$$
--   Put
--   $$x=n^3\Big(\log\big(n\log|\mathcal P|+T\Phi_{\max}\big)+\log\frac{1}{2\epsilon^2}\Big).$$
--   Then for every initial state $s\in\mathcal P^n$ the mixing time satisfies $\tau_s(\epsilon)\le x$: for every time $t\in\mathbb N$ with $x<t+1$ (i.e. $t\ge\lfloor x\rfloor$) the distribution of the chain after $t$ steps is $\epsilon$-close to $\pi$,
--   $$d_{TV}\big(P^t(s,\cdot),\pi\big)\le\epsilon .$$
--   For $n=1$ the same holds for every $t\ge x$ (the bound rounded up).
--
--   The dependence on $T\Phi_{\max}$ is doubly logarithmic, compared with the $e^{\Omega(T\Phi_{\max})}$ mixing of the plain logit dynamics.
--
--   **Formalization Note** The total variation distance is $\max_{A}|\mu(A)-\nu(A)|$ (the published `MarkovMixing.tvDist`) and $P^t(s,\cdot)$ is the row of the $t$-th matrix power (`MarkovMixing.rowDist`).
--
--   Differences from the source:
--   - encoding: an extension parallel network G with o,d-path set P → a family P of arc sets with IsEPFamily P (single arc / parallel union / arc in series); reason: the game depends on the network only through its path family; the grammar generates exactly the path families of EP networks
--   - generalization: cost functions c_e : ℤ≥0 → ℚ, non-negative and non-decreasing → c : E → ℕ → ℝ, non-negative and monotone; reason: rational costs are real costs, so the statement specializes to the paper's
--   - encoding: N = [n] (players, [k] defined for k ∈ ℤ>0) → hypothesis 0 < n; reason: the paper's implicit n ≥ 1
--   - reading: with probability 1/2 'select two players i, j uniformly at random' and swap them → a uniform ordered pair of distinct players (probability 1/(n(n−1)) each); for n = 1 the swap step is the identity; reason: App. B.3, p.30 computes P_α(s,s′) = 1/(n(n−1)); for n = 1 no pair of distinct players exists
--   - encoding: ε-close (ε > 0 implicit, cf. Theorem 4.2 'Let ǫ > 0') → hypothesis 0 < ε; reason: the paper's implicit assumption
--   - encoding: τ_s(ǫ) ≤ x with τ_s(ǫ) = min{t : Δ_s(t′) ≤ ǫ ∀ t′ ≥ t} → every t ∈ ℕ with x < t + 1 has d_TV(P^t(s,·), π) ≤ ε; reason: τ_s(ǫ) is a natural number, so τ_s(ǫ) ≤ x iff τ_s(ǫ) ≤ ⌊x⌋ iff Δ_s(t) ≤ ǫ for all t ≥ ⌊x⌋, for every x ≥ 0; for x < 0 the printed inequality is impossible and the Lean form asks Δ_s(t) ≤ ε for every t
--   - correction: τ_s(ǫ) ≤ n³(log n + log log|P| + log(2TΦmax/ǫ²)) → threshold n³(log(n log|P| + TΦmax) + log(1/(2ε²))); reason: false as printed when TΦmax is small: n = 2, two parallel arcs, c ≡ 10⁻³, T = 1, ε = 1/4, s = (a, b) gives a negative bound while d_TV(P⁰(s,·), π) = 3/4; the corrected bound is the one of the paper's last step (log log π(s)⁻¹ ≤ log(n log|P| + TΦmax)) and is at most the printed one whenever |P| ≥ 2 and TΦmax ≥ 1/2
--   - correction: at n = 1, τ_s(ǫ) ≤ x (Δ_s(t) ≤ ε for every t ≥ ⌊x⌋) → Δ_s(t) ≤ ε for every t ≥ x (hypothesis ht₁, x rounded up); reason: false at n = 1 even with the corrected x: two parallel arcs, c ≡ 0, T = 0, ε = 0.24 give x = log(log 2) + log(1/(2·0.24²)) ≈ 1.795, but the chain is ½I + ½·uniform and d_TV(P¹(s,·), π) = 1/4 > 0.24, so τ_s(0.24) = 2; for n ≥ 2 the hypothesis ht₁ is vacuous and the statement is τ_s(ǫ) ≤ x
-- source:
--   Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, Theorem 4.4, p.16 (= Theorem 1.2, p.4)

import Mathlib
import Definitions.Def_mm_mixing
import Definitions.Def_GibbsCongestion_IsEPFamily
import Definitions.Def_GibbsCongestion_potentialMax
import Definitions.Def_GibbsCongestion_gibbs
import Definitions.Def_GibbsCongestion_relaxedLogit

namespace GibbsCongestion

/-- **Theorem 4.4, corrected** (Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, Theorem 4.4, p.16; = Theorem 1.2, p.4). For an extension
parallel congestion game with common strategy set `P`, `n` players, non-negative non-decreasing
costs, temperature `T ≥ 0`, accuracy `ε > 0` and initial state `s ∈ Pⁿ`, the relaxed logit
dynamics satisfies `τ_s(ε) ≤ x := n³ (log(n log|P| + TΦmax) + log(1/(2ε²)))`: it is `ε`-close to
the Gibbs distribution at every time `t ∈ ℕ` with `x < t + 1` (that is, every `t ≥ ⌊x⌋`); for
`n = 1`, at every `t ≥ x`.

**Correction** The printed bound `n³(log n + log log|P| + log(2TΦmax/ε²))` is false when `TΦmax` is
small: for `n = 2`, two parallel arcs, `c ≡ 10⁻³`, `T = 1`, `ε = 1/4`, `s = (a, b)` it is negative,
while `d_TV(P⁰(s,·), π) = 3/4`. The bound stated here is the one given by the paper's last step
(p.18: `log log π(s)⁻¹ ≤ log(n log|P| + TΦmax)`). At `n = 1` even the corrected `τ_s(ε) ≤ x` fails:
two parallel arcs, `c ≡ 0`, `T = 0`, `ε = 0.24` give `x ≈ 1.795` but `d_TV(P¹(s,·), π) = 1/4 > ε`, so
`τ_s(ε) = 2`; there the bound is stated with `x` rounded up (`t ≥ x`).

**Formalization Note** The network is encoded by its family `P` of o,d-paths (`IsEPFamily`);
players are `Fin n` with `0 < n`; profiles are `s : Fin n → P`. Costs are real valued,
non-negative and non-decreasing (the paper's standing assumption, p.7, with `ℚ` generalized to
`ℝ`). The mixing time `τ_s(ε) = min{t : Δ_s(t') ≤ ε for all t' ≥ t}` (pp.10–11) is a natural
number, so `τ_s(ε) ≤ x` is equivalent to "`Δ_s(t) ≤ ε` for every `t ∈ ℕ` with `x < t + 1`" (hypothesis
`ht`; for `x < 0` the printed `τ_s(ε) ≤ x` is impossible and this form asks `Δ_s(t) ≤ ε` for all `t`).
Hypothesis `ht₁` is the `n = 1` correction. `MarkovMixing.tvDist μ ν` is
`max_A |μ(A) − ν(A)|` and `MarkovMixing.rowDist Q t s` is `Q^t(s, ·)`. -/
theorem relaxed_logit_mixing {E : Type*} [Fintype E] [DecidableEq E]
    (P : Finset (Finset E)) (hP : IsEPFamily P) (n : ℕ) (hn : 0 < n)
    (c : E → ℕ → ℝ) (hc_nonneg : ∀ e k, 0 ≤ c e k) (hc_mono : ∀ e, Monotone (c e))
    (T : ℝ) (hT : 0 ≤ T) (ε : ℝ) (hε : 0 < ε) (s : Fin n → P) (t : ℕ)
    (ht : (n : ℝ) ^ 3 * (Real.log ((n : ℝ) * Real.log (P.card : ℝ) + T * potentialMax P n c) +
        Real.log (1 / (2 * ε ^ 2))) < t + 1)
    (ht₁ : n = 1 → (n : ℝ) ^ 3 * (Real.log ((n : ℝ) * Real.log (P.card : ℝ) + T * potentialMax P n c) +
        Real.log (1 / (2 * ε ^ 2))) ≤ t) :
    MarkovMixing.tvDist (MarkovMixing.rowDist (relaxedLogit P n c T) t s) (gibbs P n c T) ≤ ε := by sorry

end GibbsCongestion
