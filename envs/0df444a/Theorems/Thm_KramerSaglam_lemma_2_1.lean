-- Prove2me | Theorems.Thm_KramerSaglam_lemma_2_1
-- name    : KramerSaglam.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:05:48.973925+00:00
-- url     : https://prove2.me/theorems/e1740734-d6aa-4a63-9c28-0e739fc87cd7
-- title:
--   Lemma 2.1 — facts about Tsallis and Shannon information
-- statement:
--   Let $B$ and $C$ be bits and $Z,W,U$ arbitrary random variables. Then:
--
--   1. $0\le\bar I(C\,;Z\mid U)\le\bar H(C\mid U)$ and $\bar H(C\mid U)\le H(C\mid U)\le\big(1+\bar H(C\mid U)\big)/2$.
--   2. $\bar I(C\,;Z,W\mid U)=\bar I(C\,;Z\mid U)+\bar I(C\,;W\mid Z,U)$. If $C-Z-W$ is a Markov chain, then $\bar I(C\,;W)\le\bar I(C\,;Z)$.
--   3. $\bar I(C\,;Z\mid U)\le 2\ln 2\;I(C:Z\mid U)$. If $C$ is unbiased and independent of $U$, then also $I(C:Z\mid U)\le\bar I(C\,;Z\mid U)$.
--   4. $\bar H(C)\,\bar I(B\,;C)=\bar H(B)\,\bar I(C\,;B)$. If $B$ is unbiased, then $\bar I(C\,;B)=\big(2\Pr[B=C]-1\big)^2$.
--   5. If $B$ is independent of $U$, then $\bar I(B\,;C\mid U)\,\bar H(C\mid U)\ge\bar H(B)\,\bar I(C\,;B)$.
--   6. $0\le J_p\le I_p$ for every $p\in[0,1]$.
--
--   These are the comparison and chain rules between Shannon and Tsallis information used throughout the proof.
--
--   **Formalization Note** Observed variables are sub-σ-algebras and $Z,W$ is $Z\vee W$. "$C-Z-W$ is a Markov chain" is $P[C\mid Z,W]=P[C\mid Z]$ a.s.; "independent of $U$" is independence of $\sigma(C)$ (resp. $\sigma(B)$) and $U$.
--
--   Differences from the source:
--   - encoding: arbitrary random variables Z, W, U → sub-σ-algebras contained in the ambient one, with (Z, W) the join; reason: every random variable generates one, and the quantities depend only on it
-- source:
--   Kramer, Saglam, On the most informative Boolean function under noise, arXiv:2611.05430 (held copy sha256 d787ef8d…), Lemma 2.1, p.3

import Mathlib
import Definitions.Def_KramerSaglam_Scalars
import Definitions.Def_KramerSaglam_Conditional
import Definitions.Def_KramerSaglam_Model
import Definitions.Def_KramerSaglam_PairSetup

open MeasureTheory

namespace KramerSaglam

/-- **Lemma 2.1.** D. Kramer, M. Saglam, *On the most informative Boolean function under noise*, arXiv:2611.05430 (held copy sha256 d787ef8d…), p.3, parts 1–6 in order. The bits are `B`, `C`; the arbitrary random variables
`Z`, `W`, `U` are sub-σ-algebras.

**Formalization Note.** "`C − Z − W` is a Markov chain" is `P[C | Z, W] = P[C | Z]` a.e.; "independent of `U`" is
`Indep (sigma C) U P`; `Pr[B = C]` is the mass of `(B ∩ C) ∪ (Bᶜ ∩ Cᶜ)`. Unconditional quantities are `U = ⊥`. -/
theorem lemma_2_1 {Ω : Type*} [m₀ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B C : Set Ω) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (Z W U : MeasurableSpace Ω) (hZ : Z ≤ m₀) (hW : W ≤ m₀) (hU : U ≤ m₀) :
    -- part 1
    (0 ≤ tsInfo P C Z U ∧ tsInfo P C Z U ≤ tsGiven P C U ∧
      tsGiven P C U ≤ entGiven P C U ∧ entGiven P C U ≤ (1 + tsGiven P C U) / 2) ∧
    -- part 2
    (tsInfo P C (Z ⊔ W) U = tsInfo P C Z U + tsInfo P C W (Z ⊔ U) ∧
      (condMean P C (Z ⊔ W) =ᵐ[P] condMean P C Z → tsInfo P C W ⊥ ≤ tsInfo P C Z ⊥)) ∧
    -- part 3
    (tsInfo P C Z U ≤ 2 * Real.log 2 * info P C Z U ∧
      (P.real C = 1 / 2 → ProbabilityTheory.Indep (sigma C) U P →
        info P C Z U ≤ tsInfo P C Z U)) ∧
    -- part 4
    (tsGiven P C ⊥ * tsInfo P B (sigma C) ⊥ = tsGiven P B ⊥ * tsInfo P C (sigma B) ⊥ ∧
      (P.real B = 1 / 2 →
        tsInfo P C (sigma B) ⊥ = (2 * P.real ((B ∩ C) ∪ (Bᶜ ∩ Cᶜ)) - 1) ^ 2)) ∧
    -- part 5
    (ProbabilityTheory.Indep (sigma B) U P →
      tsInfo P B (sigma C) U * tsGiven P C U ≥ tsGiven P B ⊥ * tsInfo P C (sigma B) ⊥) ∧
    -- part 6
    (∀ p ∈ Set.Icc (0 : ℝ) 1, 0 ≤ Jp p ∧ Jp p ≤ Ip p) := by sorry

end KramerSaglam
