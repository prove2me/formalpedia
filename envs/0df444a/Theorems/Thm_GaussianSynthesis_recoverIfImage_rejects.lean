-- Prove2me | Theorems.Thm_GaussianSynthesis_recoverIfImage_rejects
-- name    : GaussianSynthesis.recoverIfImage_rejects
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:11.272597+00:00
-- url     : https://prove2.me/theorems/16c442bb-4cb8-4d5a-af23-2af0e92f82a3
-- title:
--   GaussianScalarCircuits: Recover If Image rejects
-- statement:
--   Rejection is certified absence of a producer-image preimage, provided Q P = identity was proved for the full producer/decoder pair.
--
--   Canonical Gaussian arithmetic, scalar circuit normalization and exact refinement lemmas.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianScalarCircuits.lean#L567-L572). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianScalarCircuits.lean#L567-L572 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
set_option autoImplicit true
open GaussianSynthesis

theorem GaussianSynthesis.recoverIfImage_rejects {A B : Type} [DecidableEq B]
    (P : A → B) (Q : B → A) (hQP : ∀ x, Q (P x) = x) (d : B) :
    recoverIfImage P Q d = none ↔ ¬ ∃ x, P x = d := by sorry
