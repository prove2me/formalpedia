-- Prove2me | Theorems.Thm_KramerSaglam_lemma_2_2
-- name    : KramerSaglam.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:06:46.04345+00:00
-- url     : https://prove2.me/theorems/40177817-eb67-4e83-9e6a-055f4ac1f7d6
-- title:
--   Lemma 2.2 — Shannon information is at most $c(\mu)/\ln 2$ times Tsallis information
-- statement:
--   For a nonconstant bit $C$ with mean $\mu$ (so $0<\mu<1$) and every random variable $U$,
--   $$
--   I(C:U)\le\frac{c(\mu)}{\ln 2}\,\bar I(C\,;U)\qquad\text{and}\qquad \bar H(C)\,c(\mu)\le 1,
--   $$
--   where $c(\mu)=\ln(1/\mu)/(4(1-\mu)^2)$ for $\mu\ge1/2$ and $c(\mu)=c(1-\mu)$ for $\mu<1/2$.
--
--   This reverse comparison controls the term $I(C:U)$ in the second lower bound on the gap (Lemma 3.8).
--
--   Differences from the source:
--   - encoding: a random variable U → a sub-σ-algebra U contained in the ambient one; reason: the quantities depend only on the σ-algebra generated
-- source:
--   Kramer, Saglam, On the most informative Boolean function under noise, arXiv:2611.05430 (held copy sha256 d787ef8d…), Lemma 2.2, p.3

import Mathlib
import Definitions.Def_KramerSaglam_Scalars
import Definitions.Def_KramerSaglam_Conditional
import Definitions.Def_KramerSaglam_Model
import Definitions.Def_KramerSaglam_PairSetup

open MeasureTheory

namespace KramerSaglam

/-- **Lemma 2.2.** D. Kramer, M. Saglam, *On the most informative Boolean function under noise*, arXiv:2611.05430 (held copy sha256 d787ef8d…), p.3. For a nonconstant bit `C` with mean `μ` and every `U`:
`I(C : U) ≤ (c(μ)/ln 2) Ī(C ; U)` and `H̄(C) c(μ) ≤ 1`. -/
theorem lemma_2_2 {Ω : Type*} [m₀ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (C : Set Ω) (hC : MeasurableSet C) (hpos : 0 < P.real C) (hlt : P.real C < 1)
    (U : MeasurableSpace Ω) (hU : U ≤ m₀) :
    info P C U ⊥ ≤ cMu (P.real C) / Real.log 2 * tsInfo P C U ⊥ ∧
      tsGiven P C ⊥ * cMu (P.real C) ≤ 1 := by sorry

end KramerSaglam
