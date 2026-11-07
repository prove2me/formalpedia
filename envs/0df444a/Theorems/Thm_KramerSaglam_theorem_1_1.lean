-- Prove2me | Theorems.Thm_KramerSaglam_theorem_1_1
-- name    : KramerSaglam.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:06:09.935196+00:00
-- url     : https://prove2.me/theorems/51894a7f-6f41-4b04-8aee-f08ab2453f1d
-- title:
--   Theorem 1.1 — $I(C:X)\le Q(C)\le I(Y_1:X)$ for every bit $C$ obtained from $Y$ and every $p\in[0,1]$
-- statement:
--   Let $X$ be uniform on $\{0,1\}^n$ and let $Y$ be obtained by flipping each bit of $X$ independently with probability $p$. For a bit $C$ obtained from $Y$,
--   $$
--   I(C:X)\;\le\;Q(C)\;\le\;I(Y_1:X)
--   $$
--   for any $p\in[0,1]$, where $Q(C)=\bar I_pH(C)-(\bar I_p-I_p)\bar H(C)$ is the progressive entropy, $\bar H(C)=4\mu(1-\mu)$ for $\mu=\mathbb E[C]$, $I_p=1-H_2(p)$ and $\bar I_p=(1-2p)^2$.
--
--   The statement asserts three things: $I(C:X)\le Q(C)$; $Q(C)\le 1-H_2(p)$; and $I(Y_i:X)=1-H_2(p)$ for every coordinate $i$.
--
--   Taking the outer inequality gives the Courtade–Kumar inequality $I(C:X)\le 1-H_2(p)$; the inner bound $Q(C)$ is a sharper bound at fixed mean $\mu$.
--
--   **Formalization Note** The bit $C$ is obtained from $Y$ through a function $g:\{0,1\}^n\to[0,1]$, $P(C\mid X=x,Y=y)=g(y)$; a deterministic $C=h(Y)$ is $g=\mathbf 1_{h=1}$. Information quantities are in bits and defined through conditional expectations on any probability space carrying the model.
--
--   Differences from the source:
--   - generalization: a bit C obtained from Y (a function of Y in the abstract and the base case) → C obtained from Y through any g : {0,1}ⁿ → [0, 1] (private randomness); reason: a deterministic C is the case g = indicator
--   - generalization: X a uniform bit string of length n ≥ 1 (Y₁ exists) → every n ≥ 0; reason: at n ≥ 1 it is the source's statement; at n = 0 the first two clauses still hold and the third is empty
--   - encoding: Q(C) ≤ I(Y₁ : X) → Q(C) ≤ 1 − H₂(p) and I(Y_i : X) = 1 − H₂(p) for every coordinate i; reason: the paper's display (CK), p.1, states I(Y₁ : X) = 1 − H₂(p)
--   - encoding: random variables X, Y, C → measurable maps and an event on any probability space with the model's joint law, information through conditional expectations; reason: the quantities depend only on that law
-- source:
--   Kramer, Saglam, On the most informative Boolean function under noise, arXiv:2611.05430 (held copy sha256 d787ef8d…), Theorem 1.1, p.1 (restated p.4); display (CK) and (Q), p.1

import Mathlib
import Definitions.Def_KramerSaglam_Scalars
import Definitions.Def_KramerSaglam_Conditional
import Definitions.Def_KramerSaglam_Model
import Definitions.Def_KramerSaglam_PairSetup

open MeasureTheory

namespace KramerSaglam

/-- **Theorem 1.1.** D. Kramer, M. Saglam, *On the most informative Boolean function under noise*, arXiv:2611.05430 (held copy sha256 d787ef8d…), p.1 (restated p.4): `I(C : X) ≤ Q(C) ≤ I(Y₁ : X)` for every `p ∈ [0, 1]`.

**Formalization Note.** The bit `C` is obtained from `Y` through a soft function `g` (`IsModel`), which covers
a deterministic function of `Y` and private randomness. The conclusion states `Q(C) ≤ 1 − H₂(p)` and, for each
coordinate, `I(Y_i : X) = 1 − H₂(p)`, which is the paper's own display (CK); so `n = 0`, which has no `Y₁`, is
covered too. -/
theorem theorem_1_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) (g : GeneralCK.Cube n → ℝ)
    (X Y : Ω → GeneralCK.Cube n) (C : Set Ω) (h : IsModel P p g X Y C) :
    info P C (MeasurableSpace.comap X inferInstance) ⊥ ≤ qGiven P p C ⊥ ∧
      qGiven P p C ⊥ ≤ 1 - GeneralCK.H p ∧
      ∀ i : Fin n, info P (coordSet Y i) (MeasurableSpace.comap X inferInstance) ⊥ =
        1 - GeneralCK.H p := by sorry

end KramerSaglam
