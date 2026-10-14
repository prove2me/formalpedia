-- Prove2me | Theorems.Thm_HuWang2023_weightedMeanRedshift_mem_Icc
-- name    : HuWang2023.weightedMeanRedshift_mem_Icc
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-13T00:44:11.379306+00:00
-- url     : https://prove2.me/theorems/608404f7-5caf-4e76-a526-9c152561e8a3
-- title:
--   Eq. (6): the weighted bin redshift $\bar z$ lies within the bin
-- statement:
--   Let $S$ be a nonempty finite set of data points, with redshifts $z_n$ and nonzero errors $\sigma_n$ for $n\in S$. If every $z_n$ lies in an interval $[m, M]$, then so does the inverse-variance weighted redshift of Eq. (6):
--   $$m \le \bar z = \frac{\sum_{n\in S} z_n\sigma_n^{-2}}{\sum_{n\in S}\sigma_n^{-2}} \le M.$$
--
--   This guarantees that the effective redshift assigned to a bin in the binned $H_0$ analysis of Section 5 is a genuine redshift of that bin.
-- source:
--   Jian-Ping Hu and Fa-Yin Wang, *Hubble Tension: The Evidence of New Physics*, Universe 2023, 9(2), 94, https://doi.org/10.3390/universe9020094, Section 5, p. 12, Eq. (6)

import Mathlib
import Definitions.Def_HuWang2023_HubbleTension_Defs

namespace HuWang2023

theorem weightedMeanRedshift_mem_Icc {ι : Type} (s : Finset ι) (z σ : ι → ℝ) (m M : ℝ)
    (hs : s.Nonempty) (hσ : ∀ n ∈ s, σ n ≠ 0) (hz : ∀ n ∈ s, z n ∈ Set.Icc m M) :
    weightedMeanRedshift s z σ ∈ Set.Icc m M := by sorry

end HuWang2023
