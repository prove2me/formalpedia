-- Prove2me | Theorems.Thm_OAI_DeligneDrinfeld_CutoffPrimitiveExtract_KZ_value_lie
-- name    : OAI.DeligneDrinfeld.CutoffPrimitiveExtract.KZ_value_lie
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T18:44:54.257987+00:00
-- url     : https://prove2.me/theorems/ad651f1a-8a73-411a-8c76-8e6a00c8efc6
-- title:
--   Section 7 (OpenAI, Deligne–Drinfeld) — each homogeneous part of the truncated KZ comparison value is a Lie element
-- statement:
--   For natural numbers $0 < n \le N$, let $v_N \in Q_N$ be OpenAI's KZ comparison value in the free associative real algebra on $x, y$ truncated above length $N$ (`KZComparison.value N`: the operator logarithm, applied to $1$, of the comparison of the regularized transport of the Knizhnik–Zamolodchikov connection with its sign-flipped version, as in the bundle `Def_DeligneDrinfeldKZ`). Let $\nu_N(v_N) \in \mathbb R\langle x, y\rangle$ be its normal form (`CutoffPrimitiveExtract.normalVal`) and $\nu_N(v_N)_n$ the part of word length $n$ (`TensorProjection.piece n`). Then there is a Lie element $q \in \mathrm{Lie}_{\mathbb R}\langle x, y\rangle$, in the span of brackets of exactly $n$ generators, whose image in the free associative algebra is that part:
--
--   $$\exists\, q \in \mathrm{Lie}_{\mathbb R}\langle x, y\rangle_n:\quad \iota(q) = \nu_N(v_N)_n .$$
--
--   OpenAI, *The Deligne–Drinfeld conjecture* (September 23, 2026), §7.3, p. 37: “Both series are group-like. Their logarithms are primitive and have weight at least two, so (6.2) places these logarithms in the completed free Lie algebra on $x, y$.” This statement is OpenAI's Lean theorem `OAI.DeligneDrinfeld.CutoffPrimitiveExtract.KZ_value_lie` (`lean/OAI/Algebra/Drinfeld`, Apache-2.0), the corresponding fact for the truncated real value, weight by weight up to the cutoff. All objects are OpenAI's, from the bundles `Def_DeligneDrinfeldInternals` and `Def_DeligneDrinfeldKZ`. Published as one of the intermediate statements through which the proof of `OAI.DeligneDrinfeld.main` is checked in pieces.
-- source:
--   OpenAI, The Deligne–Drinfeld conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math/blob/main/preprints/The-Deligne-Drinfeld-conjecture-September-23-2026/paper.pdf, Section 7.3, p. 37; Lean: https://github.com/openai/math/tree/main/lean/OAI/Algebra/Drinfeld (Apache-2.0)

import Mathlib
import Definitions.Def_DeligneDrinfeldKZ

namespace OAI.DeligneDrinfeld.CutoffPrimitiveExtract

theorem KZ_value_lie (N n : ℕ) (hn : 0 < n) (hnN : n ≤ N) :
    ∃ q ∈ OAI.DeligneDrinfeld.LieGrading.homogeneousLie (fun x ↦ 1) n,
      OAI.DeligneDrinfeld.AssociativeElimination.embed q =
        (OAI.DeligneDrinfeld.TensorProjection.piece n)
          ((OAI.DeligneDrinfeld.CutoffPrimitiveExtract.normalVal N) (OAI.DeligneDrinfeld.KZComparison.value N)) := by
  sorry

end OAI.DeligneDrinfeld.CutoffPrimitiveExtract
