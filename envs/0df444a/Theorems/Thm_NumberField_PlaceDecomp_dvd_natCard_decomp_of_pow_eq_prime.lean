-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_dvd_natCard_decomp_of_pow_eq_prime
-- name    : NumberField.PlaceDecomp.dvd_natCard_decomp_of_pow_eq_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/e972834d-4689-56c7-9308-f696b98930d6
-- title:
--   A p-th root of q forces p ∣ |D_w| above q
-- statement:
--   Let $F$ be a number field (a field of characteristic zero, finite over $\mathbb{Q}$) that is Galois over $\mathbb{Q}$, and let $p$ and $q$ be prime numbers. Assume there is an element $r \in F$ with $r^{p} = q$ (the image of $q$ under the canonical map $\mathbb{N} \to F$). Let $w$ be a point of the height-one spectrum of the ring of integers $\mathcal{O}_F$, that is, a nonzero prime ideal $w.\mathrm{asIdeal}$ of $\mathcal{O}_F$, and assume that the image of $q$ in $\mathcal{O}_F$ lies in $w.\mathrm{asIdeal}$, i.e. that $w$ lies above $q$. The conclusion is that $p$ divides the cardinality of [`NumberField.PlaceDecomp.decomp ℚ F w`](def/NumberField_PlaceDecompositionAction.html#L82), the decomposition subgroup of the valuation subring of the $w$-adic valuation of $F$ inside the group $F \simeq_{\mathbb{Q}\text{-alg}} F$ of $\mathbb{Q}$-algebra automorphisms of $F$, the cardinality being taken as a natural number in the sense of `Nat.card`.
--
--   This is the statement that a number field containing a $p$-th root of a prime $q$ is ramified of index divisible by $p$ at every place above $q$, expressed through the order $|D_w| = e(w/q)\,f(w/q)$ of the decomposition group. It is used in the local analysis of $\mu_p$-valued cohomology classes over a Kummer-type field, where the local contribution at a place $w$ above $q$ is controlled by $|D_w|/p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_dvd_natCard_decomp_of_pow_eq_prime.lean

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain
open scoped NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.dvd_natCard_decomp_of_pow_eq_prime
    (F : Type) [Field F] [NumberField F] [IsGalois ℚ F]
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (r : F) (hr : r ^ p = (q : F))
    (w : HeightOneSpectrum (𝓞 F)) (hw : ((q : ℕ) : 𝓞 F) ∈ w.asIdeal) :
    p ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ F w) := by sorry
