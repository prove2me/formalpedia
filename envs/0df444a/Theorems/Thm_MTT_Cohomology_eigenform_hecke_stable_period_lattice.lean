-- Prove2me | Theorems.Thm_MTT_Cohomology_eigenform_hecke_stable_period_lattice
-- name    : MTT.Cohomology.eigenform_hecke_stable_period_lattice
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-18T21:08:32.321999+00:00
-- url     : https://prove2.me/theorems/1924ae0c-6e72-467e-acfe-49b37aacdcd2
-- title:
--   Hecke-stable integral period lattice of an eigenform
-- statement:
--   Let f be a normalized algebraic Hecke eigenform of positive level N and weight k at least two. For every prime ell, choose the two Qbar-valued compactly supported cohomology classes forming the signed Hecke eigenpacket of f. These classes may be chosen so that their normalized modular-symbol evaluations generate a nonzero finitely generated Z-submodule of Qbar which is stable under multiplication by the Hecke eigenvalue a_ell(f).
--
--   This is the integral-cohomology input: Hecke correspondences preserve the integral lattice in parabolic cohomology, while algebraic descent and the nonvanishing of periods identify the f-eigenpacket inside its scalar extension.
-- source:
--   Ash–Stevens, Modular forms in characteristic l and special values of their L-functions, Duke Math. J. 53 (1986), integral parabolic cohomology and modular symbols; together with the proved MTT cohomology nodes integral_class_hecke, eigenclass_descent, signed_evaluation, evaluation_lattice, and integral_finite_generation.

import Definitions.Def_MTT_Cohomology

set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.eigenform_hecke_stable_period_lattice
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (l : ℕ) (hl : l.Prime) :
    ∃ (ψ : Bool → Hc N (k - 2) MTT.Qbar),
      (∀ s, Packet f.epsilon f.coeff s (ψ s)) ∧
      let L : Submodule ℤ MTT.Qbar :=
        Submodule.span ℤ {v : MTT.Qbar | ∃ s j r, j ≤ k - 2 ∧
          v = evaluation j r (ψ s) / ((k - 2).choose j : MTT.Qbar)}
      L ≠ ⊥ ∧ L.FG ∧ ∀ x ∈ L, f.coeff l * x ∈ L := by
  sorry
