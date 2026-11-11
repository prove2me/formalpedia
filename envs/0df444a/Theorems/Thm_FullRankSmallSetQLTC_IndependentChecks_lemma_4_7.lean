-- Prove2me | Theorems.Thm_FullRankSmallSetQLTC_IndependentChecks_lemma_4_7
-- name    : FullRankSmallSetQLTC.IndependentChecks.lemma_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:07:10.115022+00:00
-- url     : https://prove2.me/theorems/27a50fe6-c7c3-4128-9748-34805afa386b
-- title:
--   Lemma 4.7 — distinct witnesses from disjoint prime lists
-- statement:
--   Let $P^L$ and $P^R$ be disjoint lists of $h\ge1$ distinct primes congruent to $1$ modulo $8$, and let $m\ge3$ satisfy (4.5) for the union of the $2h$ primes, $2^m>2\sqrt{\prod_{p\in P^L\cup P^R}p}$. Let $Y_L$ and $Y_R$ be the complexes of Theorem 4.6 on $G_m$ for $P^L$ and $P^R$, with common vertex set $G_m\times\mathbb F_2^h$. Then a cube of $Y_L$ and a cube of $Y_R$ share at most one vertex. When $h=2^k$, the distinct-witness condition (3.2) holds for the Hadamard incidence graphs of all signature sets.
--
--   Differences from the source:
--   - encoding: for all signature sets S_L, S_R → for all families of signatures of Y_L, Y_R indexed by arbitrary types; reason: the condition (3.2) is about pairs of cubes, so a family and its underlying set give the same condition
--   - encoding: lists of h primes; distinct-witness condition for the incidence graphs of Section 3.1 → arbitrary positive h for the cube-intersection assertion; for every k with 2^k = h, the Hadamard incidence corollary after reindexing the prime lists by Fin.cast; reason: the cube-intersection claim on p. 23 does not require Hadamard types; only the incidence construction in Section 3.1 requires h to be a power of two
--   - encoding: A(n) = {a ∈ L(ℤ) : N(a) = n, a₀ odd}/{±1} → the set APos n of representatives with positive real part; a product of classes is written sgnNorm of the product of representatives; reason: the real part of each element is odd, hence nonzero, so each class has exactly one representative with a₀ > 0; same instances
--   - encoding: π_m : 1 + 2L(ℤ₂) → Ĝ_m (reduction mod 2^m, then the quotient by scalars), Ĝ_m = U_m/R_m^×, G_m the norm ≡ 1 (mod 8) classes → pim m on integral quaternions (value 1 off the domain a ≡ 1 mod 2); U_m the units of L(ℤ/2^m) reducing to 1 mod 2; G_m the image of the units with norm ≡ 1 (mod 2^min(m,3)); reason: every quaternion the source reduces in this statement is integral and ≡ 1 (mod 2); for m ≥ 3 the groups are those of Definition 4.1
-- source:
--   Yali Aharon Holzman, Michael Ilan, Assaf Reiner, Amnon Ta-Shma, Full-Rank Constructions of Explicit Lossless Expanders and Good Small-Set qLTCs, STOC 2027 submission #692 (October 2026), Lemma 4.7, p. 23 (printed page = PDF page)

import Mathlib
import Definitions.Def_FullRankSmallSetQLTC_IndependentChecks_Quaternion
import Definitions.Def_FullRankSmallSetQLTC_IndependentChecks_Cubical

set_option autoImplicit false

namespace FullRankSmallSetQLTC.IndependentChecks

open Quaternion Pointwise

open Classical in
/-- **Lemma 4.7** (p. 23). Let `P^L = (p^L_i)`, `P^R = (p^R_i)` be disjoint lists of `h ≥ 1`
distinct primes `≡ 1 (mod 8)`, and let `m ≥ 3` satisfy (4.5) for the union of the `2h` primes.
Let `Y_L`, `Y_R` be the complexes `Cay(G_m; A_{p^L_1}^{(m)}, …)`, `Cay(G_m; A_{p^R_1}^{(m)}, …)` on
the common vertex set `G_m × 𝔽₂^h`. Then a cube of `Y_L` and a cube of `Y_R` share at most one
vertex. In particular the distinct-witness condition (3.2) holds for all signature sets
(when `h = 2^k`, the incidence graphs use the Hadamard types). -/
theorem lemma_4_7 (h : ℕ) (hh : 1 ≤ h) (PL PR : Fin h → ℕ)
    (hinj : Function.Injective (Sum.elim PL PR))
    (hpL : ∀ i, (PL i).Prime ∧ PL i % 8 = 1) (hpR : ∀ i, (PR i).Prime ∧ PR i % 8 = 1)
    (m : ℕ) (hm : 3 ≤ m)
    (hsep : 2 * Real.sqrt (((∏ i, PL i) * (∏ i, PR i) : ℕ) : ℝ) < 2 ^ m) :
    (∀ f f' : (Fin h → ZMod 2) → ↥(Gm m),
      IsCube (fun i => AredG m (PL i)) f → IsCube (fun i => AredG m (PR i)) f' →
        (Finset.univ.filter fun x => f x = f' x).card ≤ 1) ∧
    (∀ (k : ℕ) (hk : 2 ^ k = h) (ιL ιR : Type)
      (sL : ιL → Sig ↥(Gm m) (2 ^ k)) (sR : ιR → Sig ↥(Gm m) (2 ^ k)),
      (∀ σ, IsSignature (fun i => AredG m (PL (Fin.cast hk i))) (sL σ)) →
      (∀ τ, IsSignature (fun i => AredG m (PR (Fin.cast hk i))) (sR τ)) →
      DistinctWitness (k := k)
        (fun σ => normCube (fun i => AredG m (PL (Fin.cast hk i))) (sL σ))
        (fun τ => normCube (fun i => AredG m (PR (Fin.cast hk i))) (sR τ))) := by sorry

end FullRankSmallSetQLTC.IndependentChecks
