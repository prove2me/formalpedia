-- Prove2me | Theorems.Thm_GaussianSynthesis_producer_image_iff_roundtrip
-- name    : GaussianSynthesis.producer_image_iff_roundtrip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:11.272597+00:00
-- url     : https://prove2.me/theorems/67849966-ebd7-4380-9977-11db59f320a6
-- title:
--   GaussianScalarCircuits: Producer image iff roundtrip
-- statement:
--   A left-inverse decoder induces a necessary AND sufficient producer-image round-trip test. Local divisibility checks alone are not this test.
--
--   Canonical Gaussian arithmetic, scalar circuit normalization and exact refinement lemmas.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianScalarCircuits.lean#L516-L523). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianScalarCircuits.lean#L516-L523 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
set_option autoImplicit true
open GaussianSynthesis

theorem GaussianSynthesis.producer_image_iff_roundtrip {A B : Type}
    (P : A → B) (Q : B → A) (hQP : ∀ x, Q (P x) = x) (d : B) :
    (∃ x, P x = d) ↔ P (Q d) = d := by sorry
