-- Prove2me | Theorems.Thm_GaussianSynthesis_image_difference_recovers
-- name    : GaussianSynthesis.image_difference_recovers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:11.272597+00:00
-- url     : https://prove2.me/theorems/a54aaa09-4c0c-4b7a-8c8d-8d3d1e9659a5
-- title:
--   GaussianScalarCircuits: Image difference recovers
-- statement:
--   Once the complete difference is in the image, the recovered source is unique and is decoded exactly by Q.
--
--   Canonical Gaussian arithmetic, scalar circuit normalization and exact refinement lemmas.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianScalarCircuits.lean#L531-L537). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianScalarCircuits.lean#L531-L537 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
set_option autoImplicit true
open GaussianSynthesis

theorem GaussianSynthesis.image_difference_recovers {A B : Type}
    (P : A → B) (Q : B → A) (hQP : ∀ x, Q (P x) = x)
    (d : B) (x : A) (hd : d = P x) :
    Q d = x ∧ P (Q d) = d := by sorry
