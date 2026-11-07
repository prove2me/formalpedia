-- Prove2me | Theorems.Thm_GuardedSSSP_lemma_3_2
-- name    : GuardedSSSP.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:49:28.050201+00:00
-- url     : https://prove2.me/theorems/38b0adb3-d7e3-4dfe-8c5e-3641bde65583
-- title:
--   Lemma 3.2 — threshold height $D_*(x)=\log^*_2x+O(1)$
-- statement:
--   Let $T_4\ge16$. There are constants $C$ and $X$, depending only on $T_4$, such that
--
--   $$\big|D_*(x)-\log^*_2x\big|\le C\qquad\text{for every real }x\ge X.$$
--
--   Hence the generation overhead $B^{D_*(x)}$ is $\exp(O(\log^*_2x))$, the source of the factor $\exp(b\log^*_2(K+2))$ in Theorem 1.1.
--
--   Differences from the source:
--   - generalization: the fixed base threshold T₄ of Specification A.1 ("a sufficiently large integer T₄ ≥ 16") → every natural T₄ ≥ 16; reason: the statement for every T₄ ≥ 16 specializes to the paper's fixed T₄
--   - encoding: for sufficiently large x, D∗(x) = log∗₂ x + O(1) → ∃ C X ∀ x ≥ X, |D∗(x) − log∗₂ x| ≤ C; reason: the meaning of O(1) for large x
-- source:
--   Cai, Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths, STOC 2027 submission (manuscript sha256 bcda0e91…), Lemma 3.2, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_GuardedSSSP_LogHierarchy
import Definitions.Def_GuardedSSSP_Thresholds

namespace GuardedSSSP

/-- **Lemma 3.2** (Threshold height), p.7 (PDF p.8).

Bin Cai, *Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths*, STOC 2027
submission (manuscript sha256 bcda0e91…): "For sufficiently large x, D∗(x) = log∗₂ x + O(1). (15) All
constants depend only on T₄."

For every base threshold `T₄ ≥ 16` there are constants `C` and `X`, depending only on `T₄`, such that
`|D*(x) − log*₂ x| ≤ C` for every real `x ≥ X`.

**Formalization Note.** `C` and `X` are chosen after `T₄` and before `x`. -/
theorem lemma_3_2 (T4 : ℕ) (hT4 : 16 ≤ T4) :
    ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → |(Dstar T4 x : ℝ) - (logStar x : ℝ)| ≤ C := by sorry

end GuardedSSSP
