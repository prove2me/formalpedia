-- Prove2me | Theorems.Thm_NumberField_denseRange_algebraMap_infiniteAdeleRing_prod_adicCompletion
-- name    : NumberField.denseRange_algebraMap_infiniteAdeleRing_prod_adicCompletion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/1bc99b3d-fd62-5e2d-a39f-77a215722e82
-- title:
--   Weak approximation at the infinite places and a finite set S
-- statement:
--   Let $K$ be a number field, i.e. a field that is a finite extension of $\mathbb{Q}$, and let $S$ be a finite set of height-one primes of the ring of integers $\mathcal{O}_K$, that is, a finite set of finite places of $K$. Consider the map from $K$ to the product $$\mathrm{InfiniteAdeleRing}\,K \times \prod_{v \in S} K_v,$$ where the first factor is the ring of infinite adeles of $K$ (the product of the completions of $K$ at its archimedean places) and, for $v \in S$, $K_v$ denotes the $v$-adic completion of $K$; the map sends $x \in K$ to the pair consisting of the image of $x$ under the algebra map $K \to \mathrm{InfiniteAdeleRing}\,K$ and the family of images of $x$ under the algebra maps $K \to K_v$, indexed by $v \in S$. The assertion is that this map has dense range for the product topology: every nonempty open subset of $\mathrm{InfiniteAdeleRing}\,K \times \prod_{v \in S} K_v$ meets the diagonal image of $K$.
--
--   This is the weak approximation theorem of Artin–Whaples for the finitely many places of $K$ consisting of all archimedean places together with the finite set $S$, in the shape used for idelic arguments. It is invoked in the Tate-style analysis of idele class characters, where it yields that such a character is determined by its local components away from a finite set of finite places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_denseRange_algebraMap_infiniteAdeleRing_prod_adicCompletion.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.denseRange_algebraMap_infiniteAdeleRing_prod_adicCompletion
    (K : Type*) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) :
    DenseRange fun x : K =>
      (algebraMap K (InfiniteAdeleRing K) x, fun v : ↥S => algebraMap K (v.1.adicCompletion K) x) := by sorry
