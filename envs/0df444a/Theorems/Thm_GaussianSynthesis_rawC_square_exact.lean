-- Prove2me | Theorems.Thm_GaussianSynthesis_rawC_square_exact
-- name    : GaussianSynthesis.rawC_square_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:11.272597+00:00
-- url     : https://prove2.me/theorems/3b677f59-8039-489b-99a6-64e357805262
-- title:
--   GaussianScalarCircuits: Raw C square exact
-- statement:
--   C squared is swap without any parity guard when denominator tags are retained. Exact semantic restoration need not restore the original tag.
--
--   Canonical Gaussian arithmetic, scalar circuit normalization and exact refinement lemmas.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianScalarCircuits.lean#L391-L397). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianScalarCircuits.lean#L391-L397 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
set_option autoImplicit true
open GaussianSynthesis
open GaussianParity

theorem GaussianSynthesis.rawC_square_exact (u v : GInt) (e : Nat) :
    let p := rawC u v e
    let q := rawC p.left p.right p.exponent
    SameValue (packedLeft q) ⟨v,e⟩ ∧ SameValue (packedRight q) ⟨u,e⟩ := by sorry
