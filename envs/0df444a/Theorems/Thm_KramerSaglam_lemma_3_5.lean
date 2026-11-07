-- Prove2me | Theorems.Thm_KramerSaglam_lemma_3_5
-- name    : KramerSaglam.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:06:06.277018+00:00
-- url     : https://prove2.me/theorems/e65864ca-c9c3-463c-9c0e-7a49414c3423
-- title:
--   Lemma 3.5 — $\bar I(C'\,;B)\ge\bar I(C\,;B)/\bar H(C\mid U)^2$
-- statement:
--   In the setup of §3.1 with $\bar H(C\mid U)>0$, every unbiased bit $C'$ obtained from $B$ alone and satisfying the matching condition (B) also satisfies
--   $$
--   \bar I(C'\,;B)\ge\frac{\bar I(C\,;B)}{\bar H(C\mid U)^2} .
--   $$
--
--   Together with the choice $\bar I(C\,;B)\le1/4$ this lets the proof of Lemma 3.3 charge $\bar I(C\,;B)/\bar H(C\mid U)$ to $\sqrt{\bar I(C'\,;B)}$.
--
--   Differences from the source:
--   - encoding: C′ obtained from the same B → C′ with a copy (A′, B′) of (A, B) (unbiased, P(A′ △ B′) = p) on any probability space; reason: only the joint law of (B, C′) enters the statement
--   - encoding: random variable U → sub-σ-algebra U; reason: the quantities depend only on the σ-algebra generated
-- source:
--   Kramer, Saglam, On the most informative Boolean function under noise, arXiv:2611.05430 (held copy sha256 d787ef8d…), Lemma 3.5, p.5 (setup §3.1, p.4)

import Mathlib
import Definitions.Def_KramerSaglam_Scalars
import Definitions.Def_KramerSaglam_Conditional
import Definitions.Def_KramerSaglam_Model
import Definitions.Def_KramerSaglam_PairSetup

open MeasureTheory

namespace KramerSaglam

/-- **Lemma 3.5.** D. Kramer, M. Saglam, *On the most informative Boolean function under noise*, arXiv:2611.05430 (held copy sha256 d787ef8d…), p.5: every bit `C′` satisfying (B) also satisfies `Ī(C′ ; B) ≥ Ī(C ; B) / H̄(C | U)²`.

**Formalization Note.** As in Lemma 3.4, `C′` is an unbiased bit obtained from `B` alone and lives with a copy `(A′, B′)` of `(A, B)` on any
probability space. The setup's `H̄(C | U) > 0` (p.4) is `hv`. -/
theorem lemma_3_5 {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (p : ℝ) (A B : Set Ω) (U : MeasurableSpace Ω) (C : Set Ω)
    (h : IsPairSetup P p A B U C) (hv : 0 < tsGiven P C U)
    (P' : Measure Ω') [IsProbabilityMeasure P'] (A' B' C' : Set Ω') (hchain : IsChain P' p A' B' C')
    (hunb : P'.real C' = 1 / 2) (hmatch : MatchingB P B U C P' B' C') :
    tsInfo P' C' (sigma B') ⊥ ≥ tsInfo P C (sigma B) ⊥ / tsGiven P C U ^ 2 := by sorry

end KramerSaglam
