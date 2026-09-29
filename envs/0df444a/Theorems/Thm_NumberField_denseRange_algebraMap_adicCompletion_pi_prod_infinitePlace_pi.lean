-- Prove2me | Theorems.Thm_NumberField_denseRange_algebraMap_adicCompletion_pi_prod_infinitePlace_pi
-- name    : NumberField.denseRange_algebraMap_adicCompletion_pi_prod_infinitePlace_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/b2a75c7e-836c-5318-a46a-0052ba07f298
-- title:
--   Weak approximation: K dense in prod_{v∈ S}Kᵥ×prod_{w∣∞}K_w
-- statement:
--   Let $K$ be a field which is a number field, and let $S$ be a finite set of height-one primes of the ring of integers $\mathcal{O}_K$, i.e. a `Finset` of `IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)`. Consider the map from $K$ to the product of two product spaces: the first component sends $x$ to the family, indexed by the elements $v$ of $S$ (the coercion of the finset to a subtype), of the images of $x$ under the algebra map from $K$ into the $v$-adic completion $K_v$ = `v.adicCompletion K`; the second component sends $x$ to the family, indexed by *all* infinite places $w$ of $K$, of the images of $x$ under the algebra map from $K$ into the completion $K_w$ = `w.Completion`. The assertion is that this map has dense range for the product topology on $\prod_{v\in S}K_v\times\prod_{w\mid\infty}K_w$, i.e. its image meets every nonempty open set. No condition relating $S$ to the archimedean places is imposed, and the archimedean factor always comprises every infinite place.
--
--   This is the weak approximation (Artin–Whaples) statement for a number field, in the shape of simultaneous approximation at a finite set of finite places together with all archimedean places. It is used in the project to produce global elements with prescribed local behaviour, for instance in the analytic estimates for automorphic forms and in the determination of a Hecke character by its values on local uniformisers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_denseRange_algebraMap_adicCompletion_pi_prod_infinitePlace_pi.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem NumberField.denseRange_algebraMap_adicCompletion_pi_prod_infinitePlace_pi {K : Type*} [Field K] [NumberField K]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) :
    DenseRange (fun x : K =>
      ((fun v : S => algebraMap K (v.1.adicCompletion K) x),
       (fun w : NumberField.InfinitePlace K => algebraMap K w.Completion x))) := by sorry
