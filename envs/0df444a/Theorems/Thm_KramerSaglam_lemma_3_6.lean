-- Prove2me | Theorems.Thm_KramerSaglam_lemma_3_6
-- name    : KramerSaglam.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:06:06.170972+00:00
-- url     : https://prove2.me/theorems/d82fe72f-6cb4-4841-8380-363015af26b0
-- title:
--   Lemma 3.6 — $I(B:C\mid U)-I(B:C)$ is at least a product of Tsallis informations
-- statement:
--   With $A=X_i$, $B=Y_i$, $U=X_{-i}$: if $\bar H(C\mid U)>0$, then
--   $$
--   I(B:C\mid U)-I(B:C)\ge\frac{1}{2\ln 2}\cdot\frac{\bar I(C\,;B)\,\bar I(C\,;U)}{\bar H(C)\,\bar H(C\mid U)} .
--   $$
--
--   This supplies the positive term in $\bar I(C\,;U)$ of the first lower bound on the gap (Lemma 3.7).
--
--   Differences from the source:
--   - generalization: A = X_i, B = Y_i, U = X₋ᵢ in the noisy cube → any pair setup of §3.1 (A, B unbiased with P(A △ B) = p, independent of U; C obtained from (B, U)); reason: the coordinate instance is a pair setup, which is all the proof uses
--   - encoding: random variable U → sub-σ-algebra U; reason: the quantities depend only on the σ-algebra generated
-- source:
--   Kramer, Saglam, On the most informative Boolean function under noise, arXiv:2611.05430 (held copy sha256 d787ef8d…), Lemma 3.6, p.5 (shorthands p.4)

import Mathlib
import Definitions.Def_KramerSaglam_Scalars
import Definitions.Def_KramerSaglam_Conditional
import Definitions.Def_KramerSaglam_Model
import Definitions.Def_KramerSaglam_PairSetup

open MeasureTheory

namespace KramerSaglam

/-- **Lemma 3.6.** D. Kramer, M. Saglam, *On the most informative Boolean function under noise*, arXiv:2611.05430 (held copy sha256 d787ef8d…), pp.5: if `H̄(C | U) > 0`, then
`I(B : C | U) − I(B : C) ≥ (1/(2 ln 2)) Ī(C ; B) Ī(C ; U) / (H̄(C) H̄(C | U))`, on the setup of §3.1. -/
theorem lemma_3_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ) (A B : Set Ω) (U : MeasurableSpace Ω) (C : Set Ω) (h : IsPairSetup P p A B U C)
    (hv : 0 < tsGiven P C U) :
    info P B (sigma C) U - info P B (sigma C) ⊥ ≥
      1 / (2 * Real.log 2) *
        (tsInfo P C (sigma B) ⊥ * tsInfo P C U ⊥ / (tsGiven P C ⊥ * tsGiven P C U)) := by sorry

end KramerSaglam
