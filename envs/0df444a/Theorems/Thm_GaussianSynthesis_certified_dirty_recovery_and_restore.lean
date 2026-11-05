-- Prove2me | Theorems.Thm_GaussianSynthesis_certified_dirty_recovery_and_restore
-- name    : GaussianSynthesis.certified_dirty_recovery_and_restore
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:11.272597+00:00
-- url     : https://prove2.me/theorems/a17366a3-8a6e-4a0d-8924-b253aaa50f70
-- title:
--   GaussianScalarCircuits: Certified dirty recovery and restore
-- statement:
--   Abstract dirty-scratch restoration uses only the complete image test and the backend's subtraction restoration law. This separates image membership from the representation-specific arithmetic implementation.
--
--   Canonical Gaussian arithmetic, scalar circuit normalization and exact refinement lemmas.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianScalarCircuits.lean#L586-L595). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianScalarCircuits.lean#L586-L595 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
set_option autoImplicit true
open GaussianSynthesis

theorem GaussianSynthesis.certified_dirty_recovery_and_restore {A B : Type} [Sub B]
    (P : A → B) (Q : B → A) (hQP : ∀ x, Q (P x) = x)
    (old updated : B) (x : A)
    (himage : updated-old = P x)
    (hrestore : updated-(updated-old) = old) :
    Q (updated-old) = x ∧
    P (Q (updated-old)) = updated-old ∧
    updated-P (Q (updated-old)) = old := by sorry
