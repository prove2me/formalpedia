-- Prove2me | Theorems.Thm_MTT_Cohomology_signed_evaluation
-- name    : MTT.Cohomology.signed_evaluation
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-06T13:59:42.925703+00:00
-- url     : https://prove2.me/theorems/c502911d-8cbe-45cc-b1b9-0a803205f538
-- title:
--   Signed modular-symbol evaluation and Hecke eigenclasses
-- statement:
--   The two signed projections of the integration class satisfy the explicit prime-Hecke, nebentype and reflection eigenconditions. Integral coefficient evaluation recovers binomial(k−2,j) times the signed integral, including the factor 1/2 and the polynomial reflection (−1)^j. The evaluation functionals are defined over Z and extend coefficientwise.
-- source:
--   Ash–Stevens, Modular forms in characteristic l and special values of their L-functions (1986), §4, Definition 4.1 and Proposition 4.2, pp. 861–863, https://math.bu.edu/people/ghs/papers/Mod_fms_char_ell.pdf. Integral statements use relative group cohomology, not the coarse quotient at elliptic points. Signed projection as in Williams, An introduction to p-adic L-functions II, §11.3, https://warwick.ac.uk/fac/sci/maths/people/staff/cwilliams/lecturenotes/lecture_notes_part_ii.pdf.

import Definitions.Def_MTT_Cohomology
import Mathlib.RingTheory.Flat.Basic
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.signed_evaluation
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k-2) ℂ)
    (hI : ∀ f, IntegralClass f (I f)) (hT : HeckeEquivariant I)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) :
    ∃ φ : Bool → Hc N (k-2) ℂ, ∀ s,
      SignedClass f.form s (φ s) ∧
      Packet (fun d => ι (f.epsilon d)) (fun l => ι (f.coeff l)) s (φ s) := by sorry
