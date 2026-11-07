-- Prove2me | Theorems.Thm_KramerSaglam_lemma_3_8
-- name    : KramerSaglam.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:06:08.922191+00:00
-- url     : https://prove2.me/theorems/f22c964b-52fb-42f8-a944-e8bd1e86523c
-- title:
--   Lemma 3.8 — the second lower bound (3.2) on the gap $Q(C)-I(C:X)$
-- statement:
--   With $A=X_i$, $B=Y_i$, $U=X_{-i}$, $X=(A,U)$ and $\mu=\mathbb E[C]$: if $\bar H(C\mid U)>0$ and $C'$ is an unbiased bit obtained from $B$ alone using private randomness and satisfying (B), then
--   $$
--   Q(C)-I(C:X)\ge\bar H(C\mid U)\,I(A:B\mid C')-\Big[\frac{(1-\bar I_p)\,c(\mu)}{\ln 2}+J_p\Big]\bar I(C\,;U).\tag{3.2}
--   $$
--
--   This second lower bound has a negative term in $\bar I(C\,;U)$; adding $\lambda$ times it to (3.1) cancels the $\bar I(C\,;U)$ terms.
--
--   Differences from the source:
--   - generalization: A = X_i, B = Y_i, U = X₋ᵢ in the noisy cube → any pair setup of §3.1, with X = (A, U); reason: the coordinate instance is a pair setup, which is all the proof uses
--   - encoding: C′ obtained from the same B → C′ with a copy (A′, B′) of (A, B) (unbiased, P(A′ △ B′) = p) on any probability space; reason: only the joint law of (A, B, C′) enters the statement
--   - encoding: random variable U → sub-σ-algebra U; reason: the quantities depend only on the σ-algebra generated
-- source:
--   Kramer, Saglam, On the most informative Boolean function under noise, arXiv:2611.05430 (held copy sha256 d787ef8d…), Lemma 3.8, display (3.2), p.6

import Mathlib
import Definitions.Def_KramerSaglam_Scalars
import Definitions.Def_KramerSaglam_Conditional
import Definitions.Def_KramerSaglam_Model
import Definitions.Def_KramerSaglam_PairSetup

open MeasureTheory

namespace KramerSaglam

/-- **Lemma 3.8.** D. Kramer, M. Saglam, *On the most informative Boolean function under noise*, arXiv:2611.05430 (held copy sha256 d787ef8d…), p.6, display (3.2). `X` is `sigma A ⊔ U`, `μ = P(C)`, and `C′` is as in Lemma 3.7. -/
theorem lemma_3_8 {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (p : ℝ) (A B : Set Ω) (U : MeasurableSpace Ω) (C : Set Ω)
    (h : IsPairSetup P p A B U C) (hv : 0 < tsGiven P C U)
    (P' : Measure Ω') [IsProbabilityMeasure P'] (A' B' C' : Set Ω') (hchain : IsChain P' p A' B' C')
    (hunb : P'.real C' = 1 / 2) (hmatch : MatchingB P B U C P' B' C') :
    qGiven P p C ⊥ - info P C (sigma A ⊔ U) ⊥ ≥
      tsGiven P C U * info P' A' (sigma B') (sigma C') -
        ((1 - IpBar p) * cMu (P.real C) / Real.log 2 + Jp p) * tsInfo P C U ⊥ := by sorry

end KramerSaglam
