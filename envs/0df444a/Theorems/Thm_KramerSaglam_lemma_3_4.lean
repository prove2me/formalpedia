-- Prove2me | Theorems.Thm_KramerSaglam_lemma_3_4
-- name    : KramerSaglam.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:06:12.894209+00:00
-- url     : https://prove2.me/theorems/7d2b5446-da94-4550-843f-305d4018260f
-- title:
--   Lemma 3.4 — a matching bit $C'$ exists and $I(A:C')\ge I(A:C\mid U)/\bar H(C\mid U)$
-- statement:
--   In the setup of §3.1 ($U$ a random variable, $A,B$ unbiased bits with $P(A\ne B)=p$ jointly independent of $U$, $C$ a bit obtained from $(B,U)$ using private randomness, with $\bar H(C\mid U)>0$), consider unbiased bits $C'$ obtained from $B$ alone using private randomness, subject to the matching condition
--   $$
--   I(B:C')=\frac{I(B:C\mid U)}{\bar H(C\mid U)} .\tag{B}
--   $$
--   A bit $C'$ satisfying (B) exists, and every such bit satisfies
--   $$
--   I(A:C')\ge\frac{I(A:C\mid U)}{\bar H(C\mid U)} .
--   $$
--
--   **Formalization Note** Existence is asserted on some probability space carrying a copy $(A',B')$ of $(A,B)$, with the same channel $p$, and an unbiased $C'$ with $A'-B'-C'$ a Markov chain; the universal clause ranges over all such triples on any probability space.
--
--   Differences from the source:
--   - encoding: C′ obtained from the same B → C′ with a copy (A′, B′) of (A, B) (unbiased, P(A′ △ B′) = p) on any probability space; reason: only the joint law of (A, B, C′) enters the statement
--   - encoding: random variable U → sub-σ-algebra U; reason: the quantities depend only on the σ-algebra generated
-- source:
--   Kramer, Saglam, On the most informative Boolean function under noise, arXiv:2611.05430 (held copy sha256 d787ef8d…), §3.1 setup, display (B) and Lemma 3.4, p.4

import Mathlib
import Definitions.Def_KramerSaglam_Scalars
import Definitions.Def_KramerSaglam_Conditional
import Definitions.Def_KramerSaglam_Model
import Definitions.Def_KramerSaglam_PairSetup

open MeasureTheory
universe v

namespace KramerSaglam

/-- **Lemma 3.4.** D. Kramer, M. Saglam, *On the most informative Boolean function under noise*, arXiv:2611.05430 (held copy sha256 d787ef8d…), p.4: a bit `C′` satisfying (B) exists, and every such bit satisfies
`I(A : C′) ≥ I(A : C | U) / H̄(C | U)`.

**Formalization Note.** `C′` is an unbiased bit obtained from `B` alone. Only the law of `(A, B, C′)` matters, so it may live on any
probability space, with a copy `(A′, B′)` of `(A, B)` having the same channel `p`. -/
theorem lemma_3_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ) (A B : Set Ω) (U : MeasurableSpace Ω) (C : Set Ω) (h : IsPairSetup P p A B U C)
    (hv : 0 < tsGiven P C U) :
    (∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (A' B' C' : Set Ω'), IsChain P' p A' B' C' ∧ P'.real C' = 1 / 2 ∧ MatchingB P B U C P' B' C') ∧
    (∀ (Ω' : Type v) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P'] (A' B' C' : Set Ω'),
      IsChain P' p A' B' C' → P'.real C' = 1 / 2 → MatchingB P B U C P' B' C' →
        info P' A' (sigma C') ⊥ ≥ info P A (sigma C) U / tsGiven P C U) := by sorry

end KramerSaglam
