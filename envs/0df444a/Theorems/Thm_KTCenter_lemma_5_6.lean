-- Prove2me | Theorems.Thm_KTCenter_lemma_5_6
-- name    : KTCenter.lemma_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:30:56.57536+00:00
-- url     : https://prove2.me/theorems/203b9f9a-301a-4cff-8dec-1712d6eb122e
-- title:
--   Lemma 5.6 — $\mathcal B$ partitions $U$ and $\sum_B|B|^2\le C_0W$
-- statement:
--   Let $(w_v)$ be nonnegative integers, $0<\beta<1$, $0<\zeta<1$. The family $\mathcal B$ of Algorithm 3 consists of pairwise disjoint nonempty subsets of $U=\{v:w_v>0\}$ whose union is $U$, and
--
--   $$\sum_{B\in\mathcal B}|B|^2\le C_0W,\qquad C_0=\frac{24M}{\zeta}+1.$$
--
--   Differences from the source:
--
--   - generalization: allowances w_v = 5 deg_{E_J}(v) of the fixed tuple → arbitrary nonnegative integers w_v; reason: Algorithms 2 and 3 take arbitrary nonnegative integer allowances and the proofs use nothing else; it specializes to the source
-- source:
--   Chakraborty, Das, Mukherjee, Kendall–tau Center Admits a PTAS, STOC 2027 submission (manuscript sha256 4739ffba…), Lemma 5.6, p.34 (PDF p.36)

import Mathlib
import Definitions.Def_KTCenter_KeyDomains
import Definitions.Def_KTCenter_PartitionCosts

namespace KTCenter

/-- **Lemma 5.6** (Partition and sum of squared subset sizes), p.34 (PDF p.36).

Chakraborty, Das, Mukherjee, *Kendall–tau Center Admits a PTAS*, STOC 2027 submission (manuscript
sha256 4739ffba…).

**Formalization Note.** Algorithms 2 and 3 for any allowances `w`. -/
theorem lemma_5_6 {d : ℕ} (w : Fin d → ℕ) (β ζ : ℚ) (hβ0 : 0 < β) (hβ1 : β < 1) (hζ0 : 0 < ζ)
    (hζ1 : ζ < 1) :
    (∀ B ∈ PartitionCosts.blocks w β ζ, B.Nonempty ∧ B ⊆ PartitionCosts.varSet w) ∧
    (↑(PartitionCosts.blocks w β ζ) : Set (Finset (Fin d))).PairwiseDisjoint id ∧
    (PartitionCosts.blocks w β ζ).biUnion id = PartitionCosts.varSet w ∧
    ((∑ B ∈ PartitionCosts.blocks w β ζ, B.card ^ 2 : ℕ) : ℚ) ≤
      PartitionCosts.constC0 ζ * (totalW w : ℚ) := by sorry

end KTCenter
