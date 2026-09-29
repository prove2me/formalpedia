-- Prove2me | Theorems.Thm_ModularCurve_placeWidthChar_mul_correspondence_heckeAlphaC_heckeBetaC_single_comm_of_prime
-- name    : ModularCurve.placeWidthChar_mul_correspondence_heckeAlphaC_heckeBetaC_single_comm_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/230af521-5d37-5abd-8ca4-06c07bb28fdb
-- title:
--   Weighted symmetry of the degree-s Hecke correspondence matrix
-- statement:
--   Fix natural numbers $M$, $s$, $q'$ with $M$ and $s$ nonzero, $s$ prime and $q'$ prime, such that $s \neq q'$, $q' \nmid M$ and $s \nmid M$, and let $k$ be an algebraically closed field of characteristic $q'$. Write $F_M =$ `modularFunctionFieldC k M` for the intermediate field of $k((q))$ generated over $k$ by `jqModC k` and `jqNModC k M`, and let `charLDegeneracyRoof k M s` be the intermediate field generated over $k$ by `jqModC k`, `jqNModC k M`, `jqNModC k s` and `jqNModC k (M * s)`; the roof is assumed to satisfy `HasPrincipalDivisors`, i.e. every nonzero element of it is the divisor of a degree-zero divisor recording its order at every place. Assume the two $k$-algebra maps $F_M \to$ `charLDegeneracyRoof k M s`, namely the inclusion `heckeAlphaC` and the substitution map `heckeBetaC`, are integral ring homomorphisms (`HeckeAlphaCIntegral`, `HeckeBetaCIntegral`). Let $\mathcal{T}$ denote the associated correspondence on divisors of $F_M$, the pullback along `heckeAlphaC` followed by the pushforward along `heckeBetaC`. For the width function $w =$ `placeWidthChar q' M`, the value of `jWidthChar q'` at the $j$-coordinate `jGeomGen k M` of a place divided by that place's ramification index `placeRamificationJ M` over the $j$-line, the conclusion is that for all places $v$, $t$ of $F_M$ one has $w(v)\,\mathcal{T}(\,[t]\,)(v) = w(t)\,\mathcal{T}(\,[v]\,)(t)$ in $\mathbb{Z}$, where $[t]$ is the prime divisor `Finsupp.single t 1`.
--
--   This is the weighted symmetry relation $w_i B_{ij} = w_j B_{ji}$ familiar from Eichler's theory of Brandt matrices, here in the form of a symmetry of the matrix of the degree-$s$ Hecke correspondence on places of the level-$M$ modular function field in characteristic $q'$, the weights being the characteristic-$q'$ widths (orders of the reduced automorphism groups of the corresponding objects). It feeds the adjointness and row-sum identities for Hecke actions on supersingular place data and on specialisations of modular curves, and the Čerednik–Drinfeld transport of Hecke correspondences.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_placeWidthChar_mul_correspondence_heckeAlphaC_heckeBetaC_single_comm_of_prime.lean

import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_PlaceWidthChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicCurve ModularCurve

theorem ModularCurve.placeWidthChar_mul_correspondence_heckeAlphaC_heckeBetaC_single_comm_of_prime
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) [Fact q'.Prime]
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    {k : Type*} [Field k] [CharP k q'] [IsAlgClosed k] [DecidableEq k]
    [HasPrincipalDivisors k ↥(charLDegeneracyRoof k M s)]
    (hα : HeckeAlphaCIntegral k M s) (hβ : HeckeBetaCIntegral k M s)
    (v t : Place k ↥(modularFunctionFieldC k M)) :
    (placeWidthChar q' M v : ℤ)
        * Divisor.correspondence (heckeAlphaC k M s) (heckeBetaC k M s) hα hβ (Finsupp.single t 1) v
      = (placeWidthChar q' M t : ℤ)
        * Divisor.correspondence (heckeAlphaC k M s) (heckeBetaC k M s) hα hβ (Finsupp.single v 1) t := by sorry
