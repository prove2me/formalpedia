-- Prove2me | Theorems.Thm_KramerSaglam_lemma_3_3
-- name    : KramerSaglam.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:06:17.629936+00:00
-- url     : https://prove2.me/theorems/50eb5bc6-48af-472a-bb99-b1c99d6583ed
-- title:
--   Lemma 3.3 — the induction step $Q(C)-I(C:X)\ge\frac1{1+\lambda}\big(Q(C\mid B)-I(C:X\mid B)\big)$
-- statement:
--   With $A=X_i$, $B=Y_i$, $U=X_{-i}$ and $X=(A,U)$: assuming $\bar I(C\,;B)\le1/4$,
--   $$
--   Q(C)-I(C:X)\ge\frac{1}{1+\lambda}\big(Q(C\mid B)-I(C:X\mid B)\big)
--   $$
--   for some $\lambda\ge0$.
--
--   This is the crux of the induction on $n$: the conditional gap on the right is nonnegative by the induction hypothesis applied to $B=0$ and $B=1$, so the gap on the left is nonnegative.
--
--   **Formalization Note** No assumption $\bar H(C\mid U)>0$ and no restriction on $p$ beyond the setup: the page's proof treats $p\in\{0,\tfrac12,1\}$, $p>\tfrac12$ and $\bar I(C\,;B)=0$ separately. The statement keeps the page's "for some $\lambda\ge0$".
--
--   Differences from the source:
--   - generalization: A = X_i, B = Y_i, U = X₋ᵢ in the noisy cube, C obtained from Y → any pair setup of §3.1 with X = (A, U); reason: the coordinate instance is a pair setup, which is all the proof uses
--   - encoding: random variable U → sub-σ-algebra U; reason: the quantities depend only on the σ-algebra generated
-- source:
--   Kramer, Saglam, On the most informative Boolean function under noise, arXiv:2611.05430 (held copy sha256 d787ef8d…), Lemma 3.3, p.4 (proof p.7)

import Mathlib
import Definitions.Def_KramerSaglam_Scalars
import Definitions.Def_KramerSaglam_Conditional
import Definitions.Def_KramerSaglam_Model
import Definitions.Def_KramerSaglam_PairSetup

open MeasureTheory

namespace KramerSaglam

/-- **Lemma 3.3.** D. Kramer, M. Saglam, *On the most informative Boolean function under noise*, arXiv:2611.05430 (held copy sha256 d787ef8d…), p.4: assuming `Ī(C ; B) ≤ 1/4`,
`Q(C) − I(C : X) ≥ (1/(1 + λ)) (Q(C | B) − I(C : X | B))` for some `λ ≥ 0`. `X` is `sigma A ⊔ U`.

**Formalization Note.** Stated on the setup of §3.1 for every `p`, which the setup confines to `[0, 1]`. The cases `p ∈ {0, 1/2, 1}` and `Ī(C ; B) = 0` are
covered, as in the proof on p.7, so `H̄(C | U) > 0` is not assumed. -/
theorem lemma_3_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ) (A B : Set Ω) (U : MeasurableSpace Ω) (C : Set Ω) (h : IsPairSetup P p A B U C)
    (hB : tsInfo P C (sigma B) ⊥ ≤ 1 / 4) :
    ∃ lam : ℝ, 0 ≤ lam ∧
      qGiven P p C ⊥ - info P C (sigma A ⊔ U) ⊥ ≥
        1 / (1 + lam) * (qGiven P p C (sigma B) - info P C (sigma A ⊔ U) (sigma B)) := by sorry

end KramerSaglam
