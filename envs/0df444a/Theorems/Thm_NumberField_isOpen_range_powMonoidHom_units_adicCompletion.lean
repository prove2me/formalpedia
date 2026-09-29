-- Prove2me | Theorems.Thm_NumberField_isOpen_range_powMonoidHom_units_adicCompletion
-- name    : NumberField.isOpen_range_powMonoidHom_units_adicCompletion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/11fcc23a-43df-5235-8d69-f214f4890790
-- title:
--   Openness of n-th powers in Kᵥ^×
-- statement:
--   Let $K$ be a number field, let $v$ be a height-one prime of the ring of integers $\mathcal{O}_K$ (an element of `IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)`), and let $n$ be a natural number with $0 < n$. Write $K_v$ for the completion `v.adicCompletion K`, a valued field carrying its valuation topology, and $K_v^\times$ for its unit group with the induced topology. The assertion is that the range of the monoid endomorphism `powMonoidHom n` of $K_v^\times$, that is the set $\{x^n : x \in K_v^\times\} = (K_v^\times)^n$, viewed as a subset of $K_v^\times$, is open. No hypothesis beyond $n \ge 1$ and the number-field and height-one-prime data is imposed; in particular $n$ is not assumed coprime to the residue characteristic of $v$.
--
--   This is the standard local statement that the subgroup of $n$-th powers is open (hence of finite index) in the multiplicative group of a non-archimedean local field. It is used in the proofs that the idelic norm has open range, [`NumberField.isOpen_range_idelicNorm`](thm.html#NumberField.isOpen_range_idelicNorm) and [`M4aHerbrand.AdeleBaseChange.isOpen_range_idelicNorm`](thm.html#M4aHerbrand.AdeleBaseChange.isOpen_range_idelicNorm).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_isOpen_range_powMonoidHom_units_adicCompletion.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem NumberField.isOpen_range_powMonoidHom_units_adicCompletion {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {n : ℕ} (hn : 0 < n) :
    IsOpen ((powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range : Set (v.adicCompletion K)ˣ) := by sorry
