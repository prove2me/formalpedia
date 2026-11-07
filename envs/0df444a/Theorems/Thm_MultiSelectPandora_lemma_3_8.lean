-- Prove2me | Theorems.Thm_MultiSelectPandora_lemma_3_8
-- name    : MultiSelectPandora.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:17:05.54777+00:00
-- url     : https://prove2.me/theorems/394739a7-22bb-4aec-bebc-8fa331af5c08
-- title:
--   Lemma 3.8 — $\mathrm{OPT}\le W(M,0)+\mathrm{OPT}_C\le2\,\mathrm{OPT}$, computable in polynomial time
-- statement:
--   For a valid instance and $k\ge1$,
--   $$\mathrm{OPT}\le W(M,0)+\mathrm{OPT}_C\le2\,\mathrm{OPT},$$
--   the better of the two policies is a 2-approximation, $\mathrm{OPT}\le2\max\{W(M,0),\mathrm{OPT}_C\}$, and $\mathrm{OPT}_C$ is the utility of a selection of at most $k$ unopened boxes. For fixed $k$, both quantities are computable in polynomial time.
--
--   This fixes the threshold $\theta$ between small and large values.
--
--   Differences from the source:
--   - reading: "polynomial in the input size, that is, in n and the total support size s", in no fixed arithmetic model → Turing.TM2ComputableInPolyTime, polynomial in the binary length of a rational input; reason: the paper fixes no model; a unit-cost model with floor is too strong to mean anything, and a cost monad would need the [FLX18a] program, which this paper does not contain
--   - encoding: Fi given explicitly, values and costs real → rational data for the machine; reason: a Turing machine reads finite words, and "given explicitly" has no other meaning for one
--   - encoding: W(M, 0) is the utility of the generalized Weitzman policy → W(M, 0) is the Bellman value; reason: fact_2_1 identifies the two
--   - reading: σi "the solution" of E[(vi − σi)+] = ci → the least solution; reason: the solution is not unique when ci = 0; κi is the same for every choice
--   - encoding: a law Fi with finite support → explicit support positions with values and probabilities, and expectations as finite sums with independence by product form; reason: p.5: "Each Fi is given explicitly, with finite support"
--   - encoding: "every constant k"; the searcher selects k prizes → k ≥ 1; reason: at k = 0 nothing can be selected, and the state has no floor
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Lemma 3.8, p.9 (PDF p.10); proof pp.29–30 (PDF pp.30–31)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_Inst_Valid
import Definitions.Def_MultiSelectPandora_Inst_mean
import Definitions.Def_MultiSelectPandora_OPT
import Definitions.Def_MultiSelectPandora_W
import Definitions.Def_MultiSelectPandora_OPTC
import Definitions.Def_MultiSelectPandora_RawInst
import Definitions.Def_MultiSelectPandora_RawInst_Valid
import Definitions.Def_MultiSelectPandora_RawInst_toInst
import Definitions.Def_MultiSelectPandora_encRawInst
import Definitions.Def_MultiSelectPandora_encRatPair

namespace MultiSelectPandora

/-- **Lemma 3.8 (constant-factor approximation)**, p.9 (PDF p.10); proof pp.29–30 (PDF pp.30–31). Beyhaghi–Han–Luqman manuscript.

`OPT ≤ W(M, 0) + OPT_C ≤ 2 OPT`, the better of the two is a 2-approximation, `OPT_C` is the utility of a selection of at most `k` closed boxes, and, for fixed `k`, both quantities are computable in polynomial time.

**Formalization Note.** That `W(M, 0)` is the utility of the Weitzman rule is `fact_2_1`. "Polynomial time" is `Turing.TM2ComputableInPolyTime` on binary rational instances. -/
theorem lemma_3_8 (k : ℕ) (hk : 1 ≤ k) :
    (∀ I : Inst, I.Valid →
      OPT I k ≤ W I Finset.univ (0 : Fin k → ℝ) + OPTC I k ∧
      W I Finset.univ (0 : Fin k → ℝ) + OPTC I k ≤ 2 * OPT I k ∧
      OPT I k ≤ 2 * max (W I Finset.univ (0 : Fin k → ℝ)) (OPTC I k) ∧
      ∃ S : Finset (Fin I.n), S.card ≤ k ∧ ∑ i ∈ S, I.mean i = OPTC I k) ∧
    ∃ f : RawInst → ℚ × ℚ,
      Nonempty (Turing.TM2ComputableInPolyTime encRawInst encRatPair f) ∧
      ∀ I : RawInst, I.Valid →
        ((f I).1 : ℝ) = W I.toInst Finset.univ (0 : Fin k → ℝ) ∧ ((f I).2 : ℝ) = OPTC I.toInst k := by sorry

end MultiSelectPandora
