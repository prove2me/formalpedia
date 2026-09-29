-- Prove2me | Theorems.Thm_MTT_Cohomology_eigenform_uniform_hecke_stable_period_lattice
-- name    : MTT.Cohomology.eigenform_uniform_hecke_stable_period_lattice
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-20T10:10:04.188529+00:00
-- url     : https://prove2.me/theorems/209986a1-f851-4bf8-ace4-2673381a147d
-- title:
--   A common Hecke-stable period lattice for an eigenform
-- statement:
--   For a normalized MTT eigenform, there is a signed parabolic-cohomology
--   packet whose normalized period values span a nonzero finitely generated
--   $\mathbf Z$-module $L\subset\overline{\mathbf Q}$, and the same lattice $L$
--   is preserved by multiplication by $a_\ell(f)$ for every prime $\ell$.
-- source:
--   The integral parabolic-cohomology lattice and prime Hecke action constructed in the MTT development.

import Definitions.Def_MTT_Cohomology

set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

/-- A single nonzero finitely generated period lattice can be chosen which is
simultaneously stable under every prime Hecke eigenscalar of an eigenform. -/
theorem MTT.Cohomology.eigenform_uniform_hecke_stable_period_lattice
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) :
    ∃ (ψ : Bool → Hc N (k - 2) MTT.Qbar),
      (∀ s, Packet f.epsilon f.coeff s (ψ s)) ∧
      let L : Submodule ℤ MTT.Qbar :=
        Submodule.span ℤ {v : MTT.Qbar | ∃ s j r, j ≤ k - 2 ∧
          v = evaluation j r (ψ s) / ((k - 2).choose j : MTT.Qbar)}
      L ≠ ⊥ ∧ L.FG ∧ ∀ l : ℕ, l.Prime → ∀ x ∈ L,
        f.coeff l * x ∈ L := by
  sorry
