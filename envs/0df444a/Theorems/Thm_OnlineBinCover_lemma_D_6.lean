-- Prove2me | Theorems.Thm_OnlineBinCover_lemma_D_6
-- name    : OnlineBinCover.lemma_D_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:55:04.969653+00:00
-- url     : https://prove2.me/theorems/d22cf72c-7f72-4a95-97c4-a55b30698c4f
-- title:
--   Lemma D.6 — every later epoch but the last has $A_{ro}(E_i)\ge\frac{|E_i|}n\mathrm{OPT}(I)-O(\frac{|E_i|}n\mathrm{OPT}(I)^{149/150})$
-- statement:
--   There are $C,c>0$ and $V_0$ such that for every instance $I$ of $n$ items with sizes in $(0,1]$ and $\mathrm{vol}(I)\ge V_0$, with probability at least $1-\exp(-c\,\mathrm{OPT}(I)^{1/60})$ over the uniform arrival order, every later epoch $E_i$ other than the last ($j<i<m$) satisfies
--
--   $$A_{ro}(E_i)\ge\frac{|E_i|}n\,\mathrm{OPT}(I)-C\,\frac{|E_i|}n\,\mathrm{OPT}(I)^{149/150},$$
--
--   where $A_{ro}(E_i)$ is the number of blueprint bins covered by the epoch's instance of Algorithm 3, for every LP solution meeting Lemma 2.2 on that instance's sample and every tie-breaking.
--
--   Summing over the later epochs gives the main theorem.
--
--   Differences from the source:
--   - generalization: $A$ counts all covered bins → the number of covered blueprint bins; reason: each covered blueprint bin is a covered bin, so the bound implies the source's for every placement of the overflow items
--   - generalization: the LP solution and the assignment choices of the algorithm → every LP solution meeting the guarantee of Lemma 2.2 on the sample and every tie-breaking priority, inside the event; reason: the proof uses only that guarantee; specializes to any fixed LP algorithm and tie-breaking
--   - encoding: $O(\cdot)$, $\Omega(\cdot)$ → absolute constants $C,c>0$ chosen before $\varepsilon$, $p$ and the instance; reason: the paper writes the dependence on $K,\varepsilon,p$ explicitly
--   - encoding: $|E_i|$ → the planned length $n_i-n_{i-1}$; reason: equal to the actual length for every epoch but the last
--   - encoding: ties resolved consistently across $I$ and its subsets → ties broken by the item label; reason: a consistent rule, as p.6 requires
-- source:
--   Ayyadevara, Khan, Kumar, Sreenivas, Optimal Online Bin Covering across Stochastic Models, STOC 2027 submission (manuscript sha256 e77e556c…), Lemma D.6, p.37 (PDF p.38)

import Mathlib
import Definitions.Def_OnlineBinCover_Epochs

namespace OnlineBinCover

/-- Lemma D.6, p.37. Ayyadevara, Khan, Kumar, Sreenivas, *Optimal Online Bin Covering across Stochastic Models*,
STOC 2027 submission (manuscript sha256 e77e556c…).

For instances of sufficiently large volume, with probability at least `1 − exp(−c OPT(I)^{1/60})`
over the arrival order, every later epoch `E_i` other than the last (`j < i < m`) satisfies
`A_ro(E_i) ≥ (|E_i|/n) OPT(I) − C (|E_i|/n) OPT(I)^{149/150}`, where `A_ro(E_i)` is the number of
covered blueprint bins of the epoch's Algorithm 3 instance, for every LP solution meeting Lemma 2.2
on that instance's sample and every tie-breaking. -/
theorem lemma_D_6 : ∃ C c V₀ : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (n : ℕ) (s : Fin n → ℝ), ValidSizes s → V₀ ≤ vol s →
      1 - Real.exp (-(c * (OPT s : ℝ) ^ ((1 : ℝ) / 60))) ≤
        DynamicOnlineLP.DLA.probPerm (fun σ : Equiv.Perm (Fin n) =>
          ∀ i : ℕ, jInit (s ∘ σ) < i → i < numEpochs (s ∘ σ) →
          ∀ x : (Fin (Kof (epochEps s σ i)) → ℕ) →₀ ℝ,
            LPSpec s (epochSample s σ i) (epochEps s σ i) x →
          ∀ prioL prioS,
            (epochLen s σ i : ℝ) / n * (OPT s : ℝ) -
                C * ((epochLen s σ i : ℝ) / n * (OPT s : ℝ) ^ ((149 : ℝ) / 150)) ≤
              (epochRun s σ i x prioL prioS : ℝ)) := by sorry

end OnlineBinCover
