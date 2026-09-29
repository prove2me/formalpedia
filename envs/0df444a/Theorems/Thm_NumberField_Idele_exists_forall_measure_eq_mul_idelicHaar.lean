-- Prove2me | Theorems.Thm_NumberField_Idele_exists_forall_measure_eq_mul_idelicHaar
-- name    : NumberField.Idele.exists_forall_measure_eq_mul_idelicHaar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/6fffda33-d956-5ea5-90b4-e4b86771fbd0
-- title:
--   Uniqueness of Haar measure on the idele group
-- statement:
--   Let $K$ be a number field, and equip the group of units $(\mathbb{A}_K^\times)$ of the adele ring `AdeleRing (𝓞 K) K` with a measurable space structure which is the Borel $\sigma$-algebra of its topology. Let $\nu$ be a measure on this group which is a Haar measure (left-invariant, finite and positive on compact sets, positive on open sets, in Mathlib's sense). The assertion is that there exists $d \in [0,\infty]$ with $d \neq 0$ and $d \neq \infty$ such that for *every* subset $s$ of the idele group — not merely every measurable one, the values being those of the associated outer measures — one has $\nu(s) = d \cdot \mu(s)$, where $\mu$ is the reference measure [`NumberField.Idele.idelicHaar K`](def/NumberField_IdeleProductMeasure.html#L391), defined as Mathlib's canonical Haar measure `Measure.haar` on $(\mathbb{A}_K^\times)$. Thus any Haar measure on the idele group is a positive finite multiple of the chosen reference Haar measure, with equality of values on arbitrary sets.
--
--   This is the uniqueness part of the Haar theorem, specialised to the idele group of a number field and stated so that comparison holds on arbitrary sets. It serves to make integrals against any Haar measure on $\mathbb{A}_K^\times$ comparable to those against the fixed reference measure, and is used in the analysis of Iwasawa-type integrals attached to automorphic forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_Idele_exists_forall_measure_eq_mul_idelicHaar.lean

import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_AdeleTopologyFacts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open scoped ENNReal

theorem NumberField.Idele.exists_forall_measure_eq_mul_idelicHaar (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (ν : Measure (AdeleRing (𝓞 K) K)ˣ) [ν.IsHaarMeasure] :
    ∃ d : ℝ≥0∞, d ≠ 0 ∧ d ≠ ⊤ ∧ ∀ s : Set (AdeleRing (𝓞 K) K)ˣ, ν s = d * NumberField.Idele.idelicHaar K s := by sorry
