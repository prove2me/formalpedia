-- Prove2me | Theorems.Thm_OnlineBinCover_lemma_D_2
-- name    : OnlineBinCover.lemma_D_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:54:08.983059+00:00
-- url     : https://prove2.me/theorems/ee1bb5d3-e4d0-4da5-8c96-1de9e7d169cb
-- title:
--   Lemma D.2 — the sample length is $s_0$ or $2s_0$ with probability $1-e^{-\Omega(\mathrm{vol}(I)^{19/20})}$
-- statement:
--   There are $c>0$ and $V_0$ such that, for every instance $I$ of $n$ items with sizes in $(0,1]$ and $\mathrm{vol}(I)\ge V_0$: let $s_0$ be the smallest power of two at least $\tfrac34 n\,\mathrm{vol}(I)^{-1/20}$; then the sample length $s$ of Algorithm 3 told $n$ satisfies
--
--   $$\Pr\big[s\in\{s_0,2s_0\}\big]\ge1-\exp\!\big(-c\,\mathrm{vol}(I)^{19/20}\big)$$
--
--   over the uniform arrival order.
--
--   Because the stopping time takes one of two deterministic values with high probability, the analysis of a fixed sample length applies.
--
--   Differences from the source:
--   - encoding: $t/n\ge\mathrm{vol}(I_\sigma(t))^{-1/19}$ in (12) → $(t/n)^{19}\mathrm{vol}(I_\sigma(t))\ge1$, and $\hat t:=n$ if no $t\le n$ satisfies it; reason: the same condition for positive volume; the default case is the paper's "never reached" and does not occur when $\mathrm{vol}(I)\ge1$
--   - encoding: the smallest power of two at least $x$ → $2^{\lceil\log_2\lceil x\rceil\rceil}$ (`Nat.clog`); reason: a power of two is an integer
--   - encoding: $O(\cdot)$, $\Omega(\cdot)$ → absolute constants $C,c>0$ chosen before $\varepsilon$, $p$ and the instance; reason: the paper writes the dependence on $K,\varepsilon,p$ explicitly
-- source:
--   Ayyadevara, Khan, Kumar, Sreenivas, Optimal Online Bin Covering across Stochastic Models, STOC 2027 submission (manuscript sha256 e77e556c…), Lemma D.2, p.33 (PDF p.34)

import Mathlib
import Definitions.Def_OnlineBinCover_Alg3

namespace OnlineBinCover

/-- Lemma D.2 (Sample length), p.33. Ayyadevara, Khan, Kumar, Sreenivas, *Optimal Online Bin Covering across Stochastic Models*,
STOC 2027 submission (manuscript sha256 e77e556c…).

Algorithm 3 told the input length `n`. For every instance of sufficiently large volume, with `s₀` the
smallest power of two at least `(3/4) n vol(I)^{-1/20}`, the sample length `s` lies in `{s₀, 2s₀}`
with probability at least `1 − exp(−c vol(I)^{19/20})` over the arrival order. -/
theorem lemma_D_2 : ∃ c V₀ : ℝ, 0 < c ∧
    ∀ (n : ℕ) (s : Fin n → ℝ), ValidSizes s → V₀ ≤ vol s →
      1 - Real.exp (-(c * vol s ^ ((19 : ℝ) / 20))) ≤
        DynamicOnlineLP.DLA.probPerm (fun σ : Equiv.Perm (Fin n) =>
          a3Len s n (List.ofFn σ) = 2 ^ Nat.clog 2 ⌈(3 / 4 : ℝ) * n * vol s ^ (-(1 : ℝ) / 20)⌉₊ ∨
          a3Len s n (List.ofFn σ) =
            2 * 2 ^ Nat.clog 2 ⌈(3 / 4 : ℝ) * n * vol s ^ (-(1 : ℝ) / 20)⌉₊) := by sorry

end OnlineBinCover
