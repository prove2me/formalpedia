-- Prove2me | Theorems.Thm_OnlineBinCover_lemma_D_5
-- name    : OnlineBinCover.lemma_D_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:54:50.568375+00:00
-- url     : https://prove2.me/theorems/81cf1484-6a4f-4793-814e-21591b94d982
-- title:
--   Lemma D.5 — every later epoch but the last has $\mathrm{OPT}(E_i)\ge\frac{|E_i|}n\mathrm{OPT}(I)-O(\frac{|E_i|}n\mathrm{OPT}(I)^{17/18})$
-- statement:
--   There are $C,c>0$ and $V_0$ such that for every instance $I$ of $n$ items with sizes in $(0,1]$ and $\mathrm{vol}(I)\ge V_0$, with probability at least $1-\exp(-c\,\mathrm{OPT}(I)^{1/60})$ over the uniform arrival order, every later epoch $E_i$ of Algorithm 4 other than the last ($j<i<m$) satisfies
--
--   $$\mathrm{OPT}(E_i)\ge\frac{|E_i|}n\,\mathrm{OPT}(I)-C\,\frac{|E_i|}n\,\mathrm{OPT}(I)^{17/18}.$$
--
--   Although the epoch boundaries depend on the arrivals, each later epoch carries its share of the optimum.
--
--   Differences from the source:
--   - encoding: $O(\cdot)$, $\Omega(\cdot)$ → absolute constants $C,c>0$ chosen before $\varepsilon$, $p$ and the instance; reason: the paper writes the dependence on $K,\varepsilon,p$ explicitly
--   - encoding: $|E_i|$ → the planned length $n_i-n_{i-1}$; reason: equal to the actual length for every epoch but the last
--   - encoding: $j$, $m$ of p.34 → `jInit`, `numEpochs`, with $j:=m$ if its defining set is empty; reason: the set is nonempty for $\mathrm{vol}(I)\ge1$
--   - encoding: ties resolved consistently across $I$ and its subsets → ties broken by the item label; reason: a consistent rule, as p.6 requires
-- source:
--   Ayyadevara, Khan, Kumar, Sreenivas, Optimal Online Bin Covering across Stochastic Models, STOC 2027 submission (manuscript sha256 e77e556c…), Lemma D.5, p.36 (PDF p.37)

import Mathlib
import Definitions.Def_OnlineBinCover_Epochs

namespace OnlineBinCover

/-- Lemma D.5, p.36. Ayyadevara, Khan, Kumar, Sreenivas, *Optimal Online Bin Covering across Stochastic Models*,
STOC 2027 submission (manuscript sha256 e77e556c…).

For instances of sufficiently large volume (standing assumption of App. D.2, p.34), with probability
at least `1 − exp(−c OPT(I)^{1/60})` over the arrival order, every later epoch `E_i` of Algorithm 4
other than the last (`j < i < m`) satisfies
`OPT(E_i) ≥ (|E_i|/n) OPT(I) − C (|E_i|/n) OPT(I)^{17/18}`. -/
theorem lemma_D_5 : ∃ C c V₀ : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (n : ℕ) (s : Fin n → ℝ), ValidSizes s → V₀ ≤ vol s →
      1 - Real.exp (-(c * (OPT s : ℝ) ^ ((1 : ℝ) / 60))) ≤
        DynamicOnlineLP.DLA.probPerm (fun σ : Equiv.Perm (Fin n) =>
          ∀ i : ℕ, jInit (s ∘ σ) < i → i < numEpochs (s ∘ σ) →
            (epochLen s σ i : ℝ) / n * (OPT s : ℝ) -
                C * ((epochLen s σ i : ℝ) / n * (OPT s : ℝ) ^ ((17 : ℝ) / 18)) ≤
              (OPTon s (epochItems s σ i) : ℝ)) := by sorry

end OnlineBinCover
