-- Prove2me | Theorems.Thm_OnlineBinCover_theorem_D_1
-- name    : OnlineBinCover.theorem_D_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:53:54.588329+00:00
-- url     : https://prove2.me/theorems/87fae71e-6ac5-48e5-96dc-94b76f632b93
-- title:
--   Theorem D.1 — Algorithm 3 covers $\mathrm{OPT}(I)-O(\mathrm{OPT}(I)^{119/120})$ bins with probability $1-e^{-\Omega(\mathrm{OPT}(I)^{3/40})}$
-- statement:
--   There are $C,c>0$ such that for every instance $I$ with sizes in $(0,1]$, with probability at least
--
--   $$1-\exp\!\big(-c\,\mathrm{OPT}(I)^{3/40}\big)$$
--
--   over the uniform arrival order, Algorithm 3 (told the input length $n$) covers at least
--
--   $$\mathrm{OPT}(I)-C\,\mathrm{OPT}(I)^{119/120}$$
--
--   blueprint bins, for every LP solution meeting Lemma 2.2 on its sample and every tie-breaking.
--
--   This removes the estimate $B$ of $\mathrm{OPT}(I)$ from the order-oblivious algorithm; Algorithm 4 applies it to each epoch.
--
--   Differences from the source:
--   - encoding: $t/n\ge\mathrm{vol}(I_\sigma(t))^{-1/19}$ in (12) → $(t/n)^{19}\mathrm{vol}(I_\sigma(t))\ge1$, and $\hat t:=n$ if no $t\le n$ satisfies it; reason: the same condition for positive volume; the default case is the paper's "never reached" and does not occur when $\mathrm{vol}(I)\ge1$
--   - generalization: $A$ counts all covered bins → the number of covered blueprint bins; reason: each covered blueprint bin is a covered bin, so the bound implies the source's for every placement of the overflow items
--   - generalization: the LP solution and the assignment choices of the algorithm → every LP solution meeting the guarantee of Lemma 2.2 on the sample and every tie-breaking priority, inside the event; reason: the proof uses only that guarantee; specializes to any fixed LP algorithm and tie-breaking
--   - encoding: the arbitrary bin of an unplaced item; $\varepsilon$ at an empty sample → an overflow bin outside the blueprint; $\varepsilon=1$; reason: only blueprint bins are counted; an empty sample covers nothing
--   - encoding: $O(\cdot)$, $\Omega(\cdot)$ → absolute constants $C,c>0$ chosen before $\varepsilon$, $p$ and the instance; reason: the paper writes the dependence on $K,\varepsilon,p$ explicitly
--   - encoding: ties resolved consistently across $I$ and its subsets → ties broken by the item label; reason: a consistent rule, as p.6 requires
-- source:
--   Ayyadevara, Khan, Kumar, Sreenivas, Optimal Online Bin Covering across Stochastic Models, STOC 2027 submission (manuscript sha256 e77e556c…), Theorem D.1, p.32 (PDF p.33)

import Mathlib
import Definitions.Def_OnlineBinCover_Alg3

namespace OnlineBinCover

/-- Theorem D.1, p.32. Ayyadevara, Khan, Kumar, Sreenivas, *Optimal Online Bin Covering across Stochastic Models*,
STOC 2027 submission (manuscript sha256 e77e556c…).

There are `C, c > 0` such that for every instance with sizes in `(0,1]`, with probability at least
`1 − exp(−c OPT(I)^{3/40})` over the arrival order, Algorithm 3 (told `n`) covers at least
`OPT(I) − C OPT(I)^{119/120}` blueprint bins, for every LP solution meeting Lemma 2.2 on its sample
and every tie-breaking. -/
theorem theorem_D_1 : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (n : ℕ) (s : Fin n → ℝ), ValidSizes s →
      1 - Real.exp (-(c * (OPT s : ℝ) ^ ((3 : ℝ) / 40))) ≤
        DynamicOnlineLP.DLA.probPerm (fun σ : Equiv.Perm (Fin n) =>
          ∀ x : (Fin (Kof (a3Eps s n (List.ofFn σ))) → ℕ) →₀ ℝ,
            LPSpec s (a3Sample s n (List.ofFn σ)) (a3Eps s n (List.ofFn σ)) x →
          ∀ prioL prioS,
            (OPT s : ℝ) - C * (OPT s : ℝ) ^ ((119 : ℝ) / 120) ≤
              (alg3 s n (List.ofFn σ) x prioL prioS : ℝ)) := by sorry

end OnlineBinCover
