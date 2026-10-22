-- Prove2me | Theorems.Thm_FullFormalization_bestOf_cons
-- name    : FullFormalization.bestOf_cons
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-09T05:31:21.472485+00:00
-- url     : https://prove2.me/theorems/2b9aae1a-3be3-4a14-8c50-3beb592fbad3
-- title:
--   Unfolding the strict-improvement accumulator on a nonempty query list
-- statement:
--   For an oracle $o$, a first query $x$ and a remaining list $xs$, the accumulator that keeps the queried point of least observed value unfolds as
--   $$\mathrm{bestOf}\bigl(o,\; x :: xs\bigr) = \mathrm{foldl}\bigl(\mathrm{bestStep}(o)\bigr)\bigl(\mathrm{some}\,x\bigr)(xs).$$
--   Here $o$ is the black-box oracle, $\mathrm{bestStep}(o)$ is one strict-improvement comparison in which the incumbent is replaced only when the newly queried value is strictly smaller, and seeding the fold with $\mathrm{some}\,x$ reflects the frozen loop's convention that the first query becomes the incumbent because its running best value starts out undefined.
-- source:
--   《有理动量 Nesterov 紧界与半径归一化五算法共同最坏情形 — 可审计完整证明稿》 (manuscript, 2026-10-08), §21 strategy 4 and §24, source lines 2177-2183; Lean: FullFormalization.RandomSearch lines 86-87

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

set_option linter.unusedSectionVars false
variable {E : Type*}

@[simp] theorem FullFormalization.bestOf_cons (o : Oracle E) (x : E) (xs : List E) :
    bestOf o (x :: xs) = xs.foldl (bestStep o) (some x) := by sorry
