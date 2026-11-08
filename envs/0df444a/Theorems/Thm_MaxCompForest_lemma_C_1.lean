-- Prove2me | Theorems.Thm_MaxCompForest_lemma_C_1
-- name    : MaxCompForest.lemma_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:38:19.065476+00:00
-- url     : https://prove2.me/theorems/f5943fc6-77ac-451b-b7a8-8a18b1c76715
-- title:
--   Lemma C.1 — exact rational weighted row facilities
-- statement:
--   There are one machine and an absolute exponent $b$ with the following property. For rational rows $x_v\in\mathbb Q^p$, positive rational weights $w_v$ and an integer $1\le s\le n$, on an input of total binary length $L$, the machine halts within $(L+2)^b$ steps and returns $s$ distinct indices $C$ with
--   $$
--   \sum_v w_v\min_{z\in C}\|x_v-x_z\|^2\le144\,\mathrm{OPT}^{\mathrm{row}}_s(x).
--   $$
--   The exponent does not depend on $p$ or $s$. This makes the existential quantization bound algorithmic, at the same center budget.
--
--   Differences from the source:
--   - reading: “a deterministic algorithm … bit time” → one Mathlib multi-stack machine `TM2ComputableAux Sym Sym` on a fixed binary encoding; reason: the paper names no machine; a bit-operation algorithm and a multi-stack machine differ by a polynomial, which the time bound absorbs with changed absolute constants
--   - encoding: $\le144\,\mathrm{OPT}^{\mathrm{row}}_s(x)$ → the cost is at most 144 times the cost of every nonempty row set of size at most $s$; reason: the same statement over a finite family
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Lemma C.1, p.36

import Mathlib
import Definitions.Def_MaxCompForest_rowCost
import Definitions.Def_MaxCompForest_rowDist
import Definitions.Def_MaxCompForest_ratFeat
import Definitions.Def_MaxCompForest_encRowIn
import Definitions.Def_MaxCompForest_encIndices
import Definitions.Def_CFLOutliers_OutputsWithin
import Definitions.Def_OnlineCRS_Combine_Sym
open OnlineCRS.Combine (Sym)
open CFLOutliers (OutputsWithin)

namespace MaxCompForest

/-- **Lemma C.1 (Exact rational weighted row facilities)**: ratio `144` against every row set of size at most
`s`, in time `(L + 2)^b` with `b` absolute, independent of `p` and `s`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), p.36.

**Formalization Note.** Rows are the columns of `x : Fin p → Fin n → ℚ`. `OPTrow_s` ranges over sets of size at
most `s` (p.7), so the bound is stated against each of them. -/
theorem lemma_C_1 :
    ∃ (M : Turing.TM2ComputableAux Sym Sym) (b : ℕ),
      ∀ (n p : ℕ) (x : Fin p → Fin n → ℚ) (w : Fin n → ℚ) (s : ℕ),
        (∀ v, 0 < w v) → 1 ≤ s → s ≤ n →
        ∃ (C : List (Fin n)) (hC : C.toFinset.Nonempty), C.Nodup ∧ C.length = s ∧
          (∀ (C' : Finset (Fin n)) (hC' : C'.Nonempty), C'.card ≤ s →
            rowCost (fun v => (w v : ℝ)) (rowDist (ratFeat x)) C.toFinset hC ≤
              144 * rowCost (fun v => (w v : ℝ)) (rowDist (ratFeat x)) C' hC') ∧
          OutputsWithin M (encRowIn x w s) (encIndices C)
            (((encRowIn x w s).length + 2) ^ b) := by sorry

end MaxCompForest
