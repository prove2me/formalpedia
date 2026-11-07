-- Prove2me | Theorems.Thm_KramerSaglam_lemma_3_7
-- name    : KramerSaglam.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:06:04.4842+00:00
-- url     : https://prove2.me/theorems/db4a2653-41e0-430b-bd21-5e8f9e92ab5f
-- title:
--   Lemma 3.7 — the first lower bound (3.1) on the gap $Q(C)-I(C:X)$
-- statement:
--   With $A=X_i$, $B=Y_i$, $U=X_{-i}$, so that $X=(A,U)$, write $\Delta=Q(C\mid B)-I(C:X\mid B)$. If $\bar H(C\mid U)>0$ and $C'$ is an unbiased bit obtained from $B$ alone using private randomness and satisfying (B), then
--   $$
--   Q(C)-I(C:X)\ge\Delta+\bar H(C\mid U)\big(\bar I_p\,I(B:C')-I(A:C')\big)+\frac{(1-\bar I_p)\,\bar I(C\,;B)\,\bar I(C\,;U)}{2\ln 2\,\bar H(C)\,\bar H(C\mid U)}-J_p\,\bar I(C\,;B).\tag{3.1}
--   $$
--
--   This is the first of the two lower bounds whose combination proves Lemma 3.3.
--
--   Differences from the source:
--   - generalization: A = X_i, B = Y_i, U = X₋ᵢ in the noisy cube → any pair setup of §3.1, with X = (A, U); reason: the coordinate instance is a pair setup, which is all the proof uses
--   - encoding: C′ obtained from the same B → C′ with a copy (A′, B′) of (A, B) (unbiased, P(A′ △ B′) = p) on any probability space; reason: only the joint law of (A, B, C′) enters the statement
--   - encoding: random variable U → sub-σ-algebra U; reason: the quantities depend only on the σ-algebra generated
-- source:
--   Kramer, Saglam, On the most informative Boolean function under noise, arXiv:2611.05430 (held copy sha256 d787ef8d…), Lemma 3.7 and the sentence before it, display (3.1), p.6; Δ p.5

import Mathlib
import Definitions.Def_KramerSaglam_Scalars
import Definitions.Def_KramerSaglam_Conditional
import Definitions.Def_KramerSaglam_Model
import Definitions.Def_KramerSaglam_PairSetup

open MeasureTheory

namespace KramerSaglam

/-- **Lemma 3.7.** D. Kramer, M. Saglam, *On the most informative Boolean function under noise*, arXiv:2611.05430 (held copy sha256 d787ef8d…), p.6, display (3.1). `X` is `sigma A ⊔ U`, and `∆ = Q(C | B) − I(C : X | B)`.

**Formalization Note.** `C′` is the bit of the sentence before the Lemma: unbiased, obtained from `B` alone, satisfying (B). As in Lemma 3.4 it
lives with a copy `(A′, B′)` of `(A, B)` on any probability space. -/
theorem lemma_3_7 {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (p : ℝ) (A B : Set Ω) (U : MeasurableSpace Ω) (C : Set Ω)
    (h : IsPairSetup P p A B U C) (hv : 0 < tsGiven P C U)
    (P' : Measure Ω') [IsProbabilityMeasure P'] (A' B' C' : Set Ω') (hchain : IsChain P' p A' B' C')
    (hunb : P'.real C' = 1 / 2) (hmatch : MatchingB P B U C P' B' C') :
    qGiven P p C ⊥ - info P C (sigma A ⊔ U) ⊥ ≥
      (qGiven P p C (sigma B) - info P C (sigma A ⊔ U) (sigma B)) +
        tsGiven P C U * (IpBar p * info P' B' (sigma C') ⊥ - info P' A' (sigma C') ⊥) +
        (1 - IpBar p) * tsInfo P C (sigma B) ⊥ * tsInfo P C U ⊥ /
          (2 * Real.log 2 * tsGiven P C ⊥ * tsGiven P C U) -
        Jp p * tsInfo P C (sigma B) ⊥ := by sorry

end KramerSaglam
