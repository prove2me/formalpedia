-- Prove2me | Theorems.Thm_KramerSaglam_lemma_3_9
-- name    : KramerSaglam.lemma_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:06:08.586493+00:00
-- url     : https://prove2.me/theorems/9e140eef-1d29-4cc2-a6e5-790099aee348
-- title:
--   Lemma 3.9 — the three-bit inequality for the unbiased chain $A-B-C'$
-- statement:
--   Let $A,B$ be unbiased bits with $P(A\ne B)=p$ and let $C'$ be an unbiased bit obtained from $B$ using private randomness. If $0<\bar I_p<1$ and $\bar I(B\,;C')>0$, then
--   $$
--   \frac{I_p-I(A:C')}{2(1+\alpha_p)}+\frac{2\big(\bar I_p\,I(B:C')-I(A:C')\big)}{\sqrt{\bar I(B\,;C')}}\ge J_p ,
--   $$
--   where $\alpha_p=J_p\ln2/(1-\bar I_p)$.
--
--   This is the inequality about three unbiased bits that remains after the comparisons of §3.1; with it the last three terms of (3.3) have a nonnegative sum.
--
--   **Formalization Note** $0<\bar I_p<1$ excludes $p\in\{0,\tfrac12,1\}$, so $\alpha_p$ is the page's.
--
--   Differences from the source:
--   - encoding: A = X_i, B = Y_i with C′ obtained from B → a chain A − B − C′ with A, B unbiased and P(A △ B) = p, C′ unbiased; reason: this is the joint law of (X_i, Y_i, C′)
-- source:
--   Kramer, Saglam, On the most informative Boolean function under noise, arXiv:2611.05430 (held copy sha256 d787ef8d…), Lemma 3.9, p.7 (restated p.12); α_p p.6

import Mathlib
import Definitions.Def_KramerSaglam_Scalars
import Definitions.Def_KramerSaglam_Conditional
import Definitions.Def_KramerSaglam_Model
import Definitions.Def_KramerSaglam_PairSetup

open MeasureTheory

namespace KramerSaglam

/-- **Lemma 3.9.** D. Kramer, M. Saglam, *On the most informative Boolean function under noise*, arXiv:2611.05430 (held copy sha256 d787ef8d…), p.7 (restated p.12). `C′` (here `C`) is an unbiased bit obtained from `B` using private randomness, so that
`A − B − C` is an unbiased Markov chain with channel `p`.

**Formalization Note.** `0 < Ī_p < 1` excludes `p ∈ {0, 1/2, 1}`, so `α_p` is the page's. -/
theorem lemma_3_9 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ) (A B C : Set Ω) (h : IsChain P p A B C) (hunb : P.real C = 1 / 2)
    (hpos : 0 < IpBar p) (hlt : IpBar p < 1) (hv : 0 < tsInfo P B (sigma C) ⊥) :
    (Ip p - info P A (sigma C) ⊥) / (2 * (1 + alphaP p)) +
        2 * (IpBar p * info P B (sigma C) ⊥ - info P A (sigma C) ⊥) /
          Real.sqrt (tsInfo P B (sigma C) ⊥) ≥ Jp p := by sorry

end KramerSaglam
