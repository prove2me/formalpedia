-- Prove2me | Theorems.Thm_Module_free_of_isWeaklyRegular_of_isRegular_ofList_eq_maximalIdeal
-- name    : Module.free_of_isWeaklyRegular_of_isRegular_ofList_eq_maximalIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/c54d8e01-22ce-5ba7-b2be-6f8464ac0a41
-- title:
--   Freeness from a full-length weakly regular sequence
-- statement:
--   Let $R$ be a commutative Noetherian local ring and let $M$ be a finitely generated $R$-module. Suppose given a list $xs$ of elements of $R$ which is a regular sequence on $R$ (in the sense of `RingTheory.Sequence.IsRegular`: weakly regular, together with the properness condition that the quotient by the ideal it generates is non-trivial) and whose generated ideal $\mathrm{Ideal.ofList}\ xs$ equals the maximal ideal of $R$; thus $R$ is regular local of dimension $xs.\mathrm{length}$. Suppose given a second list $s$ of elements of $R$ such that every member of $s$ lies in the maximal ideal, $s$ is a weakly regular sequence on $M$, $s$ has the same length as $xs$, and the quotient module $M/\bigl(\mathrm{Ideal.ofList}\ s\bigr)M$ (formally, the quotient by $\mathrm{Ideal.ofList}\ s \cdot \top$) is of finite length as an $R$-module. Then $M$ is a free $R$-module. Note that the classical hypotheses are here carried as explicit data: the regularity of $R$ is witnessed by the sequence $xs$, and the finite-length hypothesis on $M/(s)M$ is imposed rather than deduced.
--
--   This is the Auslander–Buchsbaum-type freeness criterion over a regular local ring, in a form where the regular system of parameters of $R$ and the finite length of the quotient are supplied as hypotheses. It is the commutative-algebra core of the freeness assertion in Taylor–Wiles patching, applied to the patched module over a power series ring with $xs$ taken to be a uniformiser together with the formal variables; it is used by [`Algebra.PatchingLevel.free_and_ker_eq_span`](thm.html#Algebra.PatchingLevel.free_and_ker_eq_span) and by [`MvPowerSeries.exists_coords_of_quotient_span_finite_free`](thm.html#MvPowerSeries.exists_coords_of_quotient_span_finite_free).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_free_of_isWeaklyRegular_of_isRegular_ofList_eq_maximalIdeal.lean

import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.FiniteLength
import Mathlib.LinearAlgebra.FreeModule.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem Module.free_of_isWeaklyRegular_of_isRegular_ofList_eq_maximalIdeal
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (xs : List R) (hxs : RingTheory.Sequence.IsRegular R xs)
    (hspan : Ideal.ofList xs = IsLocalRing.maximalIdeal R)
    (s : List R) (hs : ∀ r ∈ s, r ∈ IsLocalRing.maximalIdeal R)
    (hreg : RingTheory.Sequence.IsWeaklyRegular M s) (hlen : s.length = xs.length)
    (hfl : IsFiniteLength R (M ⧸ (Ideal.ofList s • ⊤ : Submodule R M))) :
    Module.Free R M := by sorry
