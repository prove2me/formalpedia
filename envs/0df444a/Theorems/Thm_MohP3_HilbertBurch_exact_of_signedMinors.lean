-- Prove2me | Theorems.Thm_MohP3_HilbertBurch_exact_of_signedMinors
-- name    : MohP3.HilbertBurch.exact_of_signedMinors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:11:41.4108+00:00
-- url     : https://prove2.me/theorems/04c967bf-dafe-4de5-9567-c2a271f1453b
-- title:
--   Hilbert Burch: exact of signed Minors
-- statement:
--   **Hilbert–Burch exactness criterion** (`4 × 3` case, over a domain).
--
--   Hypotheses: the signed maximal minors of `Φ` are `c • f` with `c` a unit; the
--   columns of `Φ` are relations on `f`; and the ideal `(f)` contains a nonzero
--   `s` and an element `t` that is a nonzerodivisor modulo `s` (so `(f)` has grade
--   at least two).  Conclusion: `Φ : S^3 → S^4` is injective and its image is the
--   kernel of `f : S^4 → S`.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L148-L246
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L148-L246

module
public import Definitions.Def_MohP3_Generic
public import Mathlib
public import Definitions.Def_MohP3_HilbertBurch
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open MohP3 MohP3.HilbertBurch
open Matrix
variable {S : Type*} [CommRing S] [IsDomain S]

theorem MohP3.HilbertBurch.exact_of_signedMinors (Φ : Matrix (Fin 4) (Fin 3) S) (f : Fin 4 → S) (c : S)
    (hc : IsUnit c)
    (hm : ∀ i : Fin 4, (-1) ^ (i : ℕ) * maximalMinor Φ i = c * f i)
    (hrel : f ᵥ* Φ = 0)
    (s t : S) (hs : s ∈ Ideal.span (Set.range f)) (ht : t ∈ Ideal.span (Set.range f))
    (hs0 : s ≠ 0)
    (hreg : ∀ u : S, t * u ∈ Ideal.span {s} → u ∈ Ideal.span {s}) :
    Function.Injective (Matrix.mulVecLin Φ) ∧
      LinearMap.range (Matrix.mulVecLin Φ) = LinearMap.ker (rowMap f) := by sorry
