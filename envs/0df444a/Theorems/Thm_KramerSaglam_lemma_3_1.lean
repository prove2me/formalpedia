-- Prove2me | Theorems.Thm_KramerSaglam_lemma_3_1
-- name    : KramerSaglam.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:06:13.825194+00:00
-- url     : https://prove2.me/theorems/e833207c-a6fb-4d5a-b38c-8830ddb21922
-- title:
--   Lemma 3.1 — the progressive entropy is at most $I(Y_1:X)$
-- statement:
--   For all $p\in[0,1]$,
--   $$
--   Q(C)\le I(Y_1:X).
--   $$
--   The statement is given in two parts:
--
--   1. for every bit $C$ on any probability space, $Q(C)=\bar I_pH(C)-J_p\bar H(C)\le 1-H_2(p)$;
--   2. in the model of Theorem 1.1, $I(Y_i:X)=1-H_2(p)$ for every coordinate $i$.
--
--   Together they give $Q(C)\le I(Y_1:X)$, the second inequality of Theorem 1.1.
--
--   Differences from the source:
--   - generalization: a bit C obtained from Y → any measurable bit C on any probability space; reason: Q(C) depends only on the mean of C and on p, and a bit obtained from Y is one such bit
--   - encoding: I(Y₁ : X) → 1 − H₂(p), with I(Y_i : X) = 1 − H₂(p) stated for every coordinate of the model; reason: the paper's display (CK), p.1, states I(Y₁ : X) = 1 − H₂(p)
-- source:
--   Kramer, Saglam, On the most informative Boolean function under noise, arXiv:2611.05430 (held copy sha256 d787ef8d…), Lemma 3.1, p.3; display (CK), p.1

import Mathlib
import Definitions.Def_KramerSaglam_Scalars
import Definitions.Def_KramerSaglam_Conditional
import Definitions.Def_KramerSaglam_Model
import Definitions.Def_KramerSaglam_PairSetup

open MeasureTheory

namespace KramerSaglam

/-- **Lemma 3.1.** D. Kramer, M. Saglam, *On the most informative Boolean function under noise*, arXiv:2611.05430 (held copy sha256 d787ef8d…), p.3: for all `p ∈ [0, 1]`, `Q(C) ≤ I(Y₁ : X)`.

**Formalization Note.** Stated as `Q(C) ≤ 1 − H₂(p)` for every bit on any probability space (`Q` depends only on the
mean of `C` and on `p`) together with `I(Y_i : X) = 1 − H₂(p)` on the model, for each coordinate; the second is the
paper's display (CK). -/
theorem lemma_3_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    (∀ C : Set Ω, MeasurableSet C → qGiven P p C ⊥ ≤ 1 - GeneralCK.H p) ∧
    (∀ {n : ℕ} (g : GeneralCK.Cube n → ℝ) (X Y : Ω → GeneralCK.Cube n) (C : Set Ω),
      IsModel P p g X Y C → ∀ i : Fin n,
        info P (coordSet Y i) (MeasurableSpace.comap X inferInstance) ⊥ = 1 - GeneralCK.H p) := by sorry

end KramerSaglam
