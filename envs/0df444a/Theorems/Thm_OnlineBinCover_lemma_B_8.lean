-- Prove2me | Theorems.Thm_OnlineBinCover_lemma_B_8
-- name    : OnlineBinCover.lemma_B_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:53:38.001349+00:00
-- url     : https://prove2.me/theorems/ec12f098-ff18-4974-9156-c6225ca648f5
-- title:
--   Lemma B.8 — $\mathrm{vol}(S^\prime)\ge(1-\mathrm{vol}(I)^{-1/6})\mathrm{vol}(S_p)/p$ when $t^\prime_M\le\tau$
-- statement:
--   In the ranges of App. B and under $R'_M<n$: for all $c_1,c_2,c_3>0$ there are $c>0$ and $V_0$ such that, for every instance with sizes in $(0,1]$ and $\mathrm{vol}(I)\ge V_0$ and every $p,\varepsilon$ in the ranges, except on an event of probability at most $\exp(-c\,p\,\mathrm{vol}(I)^{1/6})$ over the sample, whenever the sample is in the three-class case, $\mathcal E$ holds and $t'_M\le\tau=\mathrm{vol}(S_p)/(p\sqrt{\mathrm{vol}(I)})$,
--
--   $$\mathrm{vol}(S')\ge\big(1-\mathrm{vol}(I)^{-1/6}\big)\frac{\mathrm{vol}(S_p)}p.$$
--
--   When the sampled small volume is large, the small items of the input supply nearly all the S-slot demand.
--
--   Differences from the source:
--   - encoding: standing ranges $p=\Omega(\mathrm{vol}(I)^{-1/20})$, $\varepsilon=\Theta(\mathrm{vol}(I)^{-1/24})$, $\mathrm{vol}(I)$ sufficiently large (App. B, p.18) → for all $c_1,c_2,c_3>0$ there are constants and $V_0$ such that the bound holds for $p\in[c_1\mathrm{vol}(I)^{-1/20},1]$, $\varepsilon\in[c_2\mathrm{vol}(I)^{-1/24},c_3\mathrm{vol}(I)^{-1/24}]$, $\mathrm{vol}(I)\ge V_0$; reason: the paper's asymptotic standing assumption made explicit; $\varepsilon<1/8$ follows for large $V_0$
--   - encoding: $O(\cdot)$, $\Omega(\cdot)$ → absolute constants $C,c>0$ chosen before $\varepsilon$, $p$ and the instance; reason: the paper writes the dependence on $K,\varepsilon,p$ explicitly
--   - encoding: a uniformly random subset of $\lfloor pn\rfloor$ items → the first $\lfloor pn\rfloor$ arrivals of a uniform permutation, probability the fraction of the $n!$ permutations; reason: the same law
--   - encoding: "We may assume $R^\prime_M<n$" (p.23) → hypothesis $R^\prime_M<n$; reason: standing assumption of App. B.3
--   - encoding: ties resolved consistently across $I$ and its subsets → ties broken by the item label; reason: a consistent rule, as p.6 requires
--   - reading: the sampling fraction $p$ (Algorithm 2's input; $I_p$ has $\lfloor pn\rfloor$ items of $I$) → $0<p\le1$; reason: a sampling fraction of the input; this is the range the paper uses (App. B.6 takes $p<1$)
-- source:
--   Ayyadevara, Khan, Kumar, Sreenivas, Optimal Online Bin Covering across Stochastic Models, STOC 2027 submission (manuscript sha256 e77e556c…), Lemma B.8, p.24 (PDF p.25)

import Mathlib
import Definitions.Def_OnlineBinCover_EventE
import Definitions.Def_OnlineBinCover_Blueprint

namespace OnlineBinCover

/-- Lemma B.8, p.24. Ayyadevara, Khan, Kumar, Sreenivas, *Optimal Online Bin Covering across Stochastic Models*,
STOC 2027 submission (manuscript sha256 e77e556c…).

Standing ranges of App. B as in Lemma B.4 and `R′_M < n` (App. B.3, p.23). Except on an event of
probability at most `exp(−c p vol(I)^{1/6})`, whenever `E` holds (three-class case) and
`t′_M ≤ τ`, `vol(S′) ≥ (1 − vol(I)^{-1/6}) vol(Sp)/p`. -/
theorem lemma_B_8 : ∀ c₁ c₂ c₃ : ℝ, 0 < c₁ → 0 < c₂ → 0 < c₃ →
    ∃ c V₀ : ℝ, 0 < c ∧
    ∀ (n : ℕ) (s : Fin n → ℝ), ValidSizes s → V₀ ≤ vol s → ∀ p ε : ℝ,
      c₁ * vol s ^ (-(1 : ℝ) / 20) ≤ p → p ≤ 1 →
      c₂ * vol s ^ (-(1 : ℝ) / 24) ≤ ε → ε ≤ c₃ * vol s ^ (-(1 : ℝ) / 24) →
      1 - Real.exp (-(c * p * vol s ^ ((1 : ℝ) / 6))) ≤
        DynamicOnlineLP.DLA.probPerm (fun σ : Equiv.Perm (Fin n) =>
          ThreeClass s (smp σ ⌊p * n⌋₊) ε → EventE s (smp σ ⌊p * n⌋₊) ε p →
          RMprime s ε < n → tMprime s ε ≤ tau s (smp σ ⌊p * n⌋₊) ε p →
            (1 - vol s ^ (-(1 : ℝ) / 6)) * (volOn s (smallOf s (smp σ ⌊p * n⌋₊) ε) / p) ≤
              volOn s (Sprime s ε)) := by sorry

end OnlineBinCover
