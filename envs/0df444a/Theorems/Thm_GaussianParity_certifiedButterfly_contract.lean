-- Prove2me | Theorems.Thm_GaussianParity_certifiedButterfly_contract
-- name    : GaussianParity.certifiedButterfly_contract
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:10.688206+00:00
-- url     : https://prove2.me/theorems/b94d407e-e616-4e80-b358-5b142b718d36
-- title:
--   DyadicCertificates: Certified Butterfly contract
-- statement:
--   Exact Gaussian-integer parity and dyadic butterfly certificates.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/DyadicCertificates.lean#L207-L217). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/DyadicCertificates.lean#L207-L217 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Std
import Definitions.Def_DyadicCertificates
set_option autoImplicit true
open GaussianParity

theorem GaussianParity.certifiedButterfly_contract (u v : GInt) (e : Nat) :
    let p := certifiedButterfly u v e
    (p.exponent = e ∧ mulPi p.left = numeratorLeft u v ∧
      mulPi p.right = numeratorRight u v) ∨
    (p.exponent = e + 1 ∧ p.left = numeratorLeft u v ∧ p.right = numeratorRight u v) := by sorry
