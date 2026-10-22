-- Prove2me | Theorems.Thm_FullFormalization_RandomSearch_ofFn_eq_nil_iff
-- name    : FullFormalization.RandomSearch.ofFn_eq_nil_iff
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-09T05:30:54.302989+00:00
-- url     : https://prove2.me/theorems/abbb011d-b3d4-4203-85c3-5cc0adbe551f
-- title:
--   The query list of random search is empty exactly at zero budget
-- statement:
--   For a family $q$ indexed by $\mathrm{Fin}\,N$, the list formed from it is empty precisely when the index set is empty:
--   $$\bigl(\mathrm{List.ofFn}\;q : \mathrm{List}\,E\bigr) = [\,] \;\Longleftrightarrow\; N = 0 .$$
--   Here $N$ is the query budget of the fixed-seed random-search strategy and $q : \mathrm{Fin}\,N \to E$ is its predetermined list of query points. The equivalence is the length bookkeeping that lets the run be recognised as producing nothing exactly at zero budget.
-- source:
--   《有理动量 Nesterov 紧界与半径归一化五算法共同最坏情形 — 可审计完整证明稿》 (manuscript, 2026-10-08), §21 strategy 4 and §24; Lean: FullFormalization.RandomSearch lines 192-201

-- Generated from F:/20261008/FullFormalization\FullFormalization\RandomSearch.lean (Phase 3): skeleton subtraction, proof cut at
-- valStart (Stage 2), docstring stripped, declaration hoisted to top
-- level with its fully dotted name; body is `:= by sorry`.
/-
  FullFormalization.RandomSearch

  Source: `auditable_full_proof_nag_and_five_algorithm_cn.md`, section 21,
  strategy 4 (source line 2082): `fixed-seed random search`, and section 24
  (source lines 2177-2183):

      "固定 seed 后，random search 的 N 个查询点 q_1, ..., q_N 由 N, D 和公开采样
       规则完全确定，并且查询位置不依赖函数值。"

  Implementation semantics: `blackbox_algos.py`, `_random_search` and
  `_sample`:

      rng = random.Random(SAMPLE_SEED)           -- SAMPLE_SEED = 0
      for _ in range(spec.query_budget):
          point = (SAMPLE_STEP * rng.randint(-span, span) for each coordinate)
          answer = oracle.query(point)
          if best_value is None or answer["value"] < best_value:
              best_point, best_value = point, answer["value"]
      oracle.finish(best_point)

  with `SAMPLE_BOX = 8`, `SAMPLE_STEP = 1/2` and `span = int(SAMPLE_BOX /
  SAMPLE_STEP) = 16`.  The two facts that matter are:

  * the whole query list is fixed by the declared seed, the declared box and
    the declared step, hence by `(N, D)` alone — it does **not** depend on
    function values (source line 2183).  `q : Fin N → E` is therefore a
    parameter of this file, given before the function, and everything below is
    proved for *any* such fixed list.  This is the strict strengthening
    recorded in `DEPENDENCY_MAP.md` §9 D-2 and R11: the source uses only
    "fixed and independent of the function", and never any property of the
    concrete PRNG stream.  The seed-0 list of `blackbox_algos.py` is one
    instance.
  * the output is the **queried** point with the smallest observed value, and
    the comparison is strict (`<`), so on a tie the **earlier** query wins
    (`bestOf_pair_tie`).

  Nothing here uses the geometry of the sample box: the sample constants are
  recorded (`sampleBox`, `sampleStep`, `sampleSeed`, `sampleSpan`) because the
  frozen implementation declares them, but the theorems below hold for every
  predetermined query list.
-/

import Mathlib
import Definitions.Def_Coefficients
import Definitions.Def_FunctionClass
import Definitions.Def_PortfolioDefinitions
import Definitions.Def_RandomSearch

set_option linter.unusedSectionVars false

namespace FullFormalization

variable {E : Type*}

/-! ### The declared sampler constants (frozen implementation) -/











/-! ### The best observed point -/

























/-! ### Strategy 4 on a predetermined query list -/

namespace RandomSearch





























end RandomSearch

end FullFormalization

open FullFormalization
open FullFormalization.RandomSearch

set_option linter.unusedSectionVars false
variable {E : Type*}

theorem FullFormalization.RandomSearch.ofFn_eq_nil_iff {N : ℕ} (q : Fin N → E) : (List.ofFn q : List E) = [] ↔ N = 0 := by sorry
