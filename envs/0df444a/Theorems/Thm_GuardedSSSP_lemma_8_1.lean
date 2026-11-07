-- Prove2me | Theorems.Thm_GuardedSSSP_lemma_8_1
-- name    : GuardedSSSP.lemma_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:47:50.449445+00:00
-- url     : https://prove2.me/theorems/68854c9c-a5ee-437a-84dc-3fc795638447
-- title:
--   Lemma 8.1 — MaxLegalDepth returns $D_*(x)$ with $O(D_*(x)+1)$ tests and no integer above $x$
-- statement:
--   Let $T_4\ge16$. For every integer scale $x$, Algorithm 2 ($\mathrm{MaxLegalDepth}$):
--
--   1. returns $D_*(x)$ when $x\ge X_4$;
--   2. returns Small when $x<X_4$;
--   3. performs at most $C\,(D_*(x)+1)$ threshold tests when $x\ge X_4$, for an absolute constant $C$;
--   4. materializes no integer larger than $x$ other than its fixed code constants.
--
--   Its live state is the fixed tuple $(L,u,d)$, so it uses $O(1)$ scalar metadata.
--
--   The selector lets the solver choose the depth $D_*(x)$ inside the word budget, without building a tower of exponentials.
--
--   Differences from the source:
--   - generalization: the fixed base threshold T₄ of Specification A.1 ("a sufficiently large integer T₄ ≥ 16") → every natural T₄ ≥ 16; reason: the statement for every T₄ ≥ 16 specializes to the paper's fixed T₄
--   - encoding: threshold tests, live scalar metadata, materialized integers → counters returned by the instrumented procedure maxLegalDepth that follows Algorithm 2 line by line; reason: the lemma counts abstract operations of Algorithm 2
--   - generalization: O(D∗(x) + 1) threshold tests (for the paper's one fixed T₄) → ≤ C·(D∗(x)+1) for one C chosen before T₄ and x; reason: the meaning of O(·); a C uniform over every T₄ ≥ 16 specializes to the paper's fixed T₄
-- source:
--   Cai, Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths, STOC 2027 submission (manuscript sha256 bcda0e91…), Lemma 8.1 with Algorithm 2, p.17 (PDF p.18)

import Mathlib
import Definitions.Def_GuardedSSSP_Thresholds
import Definitions.Def_GuardedSSSP_maxLegalDepth

namespace GuardedSSSP

/-- **Lemma 8.1** (Selector correctness and word bound), with Algorithm 2, p.17 (PDF p.18).

Bin Cai, *Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths*, STOC 2027
submission (manuscript sha256 bcda0e91…): "The procedure returns D∗(x) when x ≥ X₄, and returns Small
otherwise. It performs O(D∗(x) + 1) threshold tests on the asymptotic region, uses O(1) live scalar
metadata, and materializes no integer larger than x except fixed code constants."

There is an absolute `C` such that for every base threshold `T₄ ≥ 16` and every integer scale `x`:
1. if `x ≥ X₄` then `MaxLegalDepth(x)` returns `D*(x)`;
2. if `x < X₄` then it returns `Small`;
3. if `x ≥ X₄` then it performs at most `C(D*(x) + 1)` threshold tests;
4. every integer it materializes, other than its fixed code constants, is at most `x`.

**Formalization Note.** `maxLegalDepth` is Algorithm 2 instrumented line by line (`none` = `Small`). Its
state is the fixed tuple `(L, u, d)`, which is the "O(1) live scalar metadata" clause. The base threshold is
any `T₄ ≥ 16`, which contains the paper's fixed "sufficiently large" `T₄` (Specification A.1). -/
theorem lemma_8_1 :
    ∃ C : ℕ, ∀ T4 : ℕ, 16 ≤ T4 → ∀ x : ℕ,
      (X4 T4 ≤ x → (maxLegalDepth T4 x).1 = some (Dstar T4 x)) ∧
      (x < X4 T4 → (maxLegalDepth T4 x).1 = none) ∧
      (X4 T4 ≤ x → (maxLegalDepth T4 x).2.1 ≤ C * (Dstar T4 x + 1)) ∧
      (maxLegalDepth T4 x).2.2 ≤ x := by sorry

end GuardedSSSP
