-- Prove2me | Theorems.Thm_GaussianParity_cross_parity_example
-- name    : GaussianParity.cross_parity_example
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:10.688206+00:00
-- url     : https://prove2.me/theorems/010f89f6-91bb-4350-ba28-a00064a6ef51
-- title:
--   DyadicCertificates: Cross parity example
-- statement:
--   The valid input pair (1,i) refutes necessity of componentwise parity.
--
--   Exact Gaussian-integer parity and dyadic butterfly certificates.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/DyadicCertificates.lean#L118-L122). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/DyadicCertificates.lean#L118-L122 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Std
import Definitions.Def_DyadicCertificates
set_option autoImplicit true
open GaussianParity

theorem GaussianParity.cross_parity_example :
    SameResidue ⟨1, 0⟩ ⟨0, 1⟩ ∧
    (⟨1, 0⟩ : GInt).re % 2 ≠ (⟨0, 1⟩ : GInt).re % 2 ∧
    butterfly ⟨1, 0⟩ ⟨0, 1⟩ = (⟨1, 1⟩, ⟨0, 0⟩) := by sorry
