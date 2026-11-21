-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_polytime_string_to_mqpt
-- name    : InfoLossLAR.WorstCase.RegevSketch.polytime_string_to_mqpt
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T08:57:49.929507+00:00
-- url     : https://prove2.me/theorems/53c9239b-e917-4706-9b70-91aeae6d7c6f
-- title:
--   Compile polynomial-time string functions to uniform quantum circuits
-- statement:
--   Let $f:\{0,1\}^*\to\{0,1\}^*$ be a deterministic polynomial-time string function. There is a uniform quantum polynomial-time multi-output circuit family $P$ such that, for any input $w$ and any event $F$ on finite binary strings closed under appending a suffix,
--
--   $$
--   f(w)\in F\quad\Longrightarrow\quad\Pr[P(w)\in F]=1.
--   $$
--
--   The family has one output length per input length, so its output may contain a suffix after $f(w)$. This general compilation interface allows deterministic classical algorithms to be used as subroutines in prefix-decoded quantum output problems.
--
--   **Formalization Note.** Polynomial time is the platform's multi-stack Turing-machine predicate; the resulting family is uniform in its fixed Clifford+T gate set. The formal inequality is $1\le\Pr[P(w)\in F]$, which is probability one when circuit well-formedness is used.
-- source:
--   Chen Qian, Information Loss Is All You Need: TC⁰ Pseudorandomness from Worst-Case Lattices, arXiv:2611.05136, Appendix I.1, pp. 132–133; generic multi-output classical-to-quantum model and encoding closure needed to formalize the finite-dimensional patch, not a verbatim theorem from that source.

import Definitions.Def_InfoLossLAR_RegevSketch_DGS

set_option autoImplicit false
open QAlgorithms.Complexity InfoLossLAR.WorstCase

namespace InfoLossLAR.WorstCase.RegevSketch

theorem polytime_string_to_mqpt (f : Str → Str) (hf : PolyTimeComputable f) :
  ∃ P : MFamily, IsMQPT P ∧ ∀ w : Str, ∀ event : Str → Prop,
    (∀ s t, event s → s <+: t → event t) → event (f w) →
      (1 : ℝ) ≤ outputProb P w event
 := by sorry

end InfoLossLAR.WorstCase.RegevSketch
