-- Prove2me | Theorems.Thm_MazurTransfer_order18_original_quotient_doubling_surjective
-- name    : MazurTransfer.order18_original_quotient_doubling_surjective
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T15:25:18.964984+00:00
-- url     : https://prove2.me/theorems/0806ad57-60fd-4c82-8069-1457f738989d
-- title:
--   Order18: unconditional doubling surjectivity from the original published Selmer arithmetic
-- statement:
--   Let \(K=\mathbb{Q}[T]/(T^3-3T-1)\) and let \(E/K\) be the original elliptic quotient with Weierstrass coefficients \((1,\tau^2+\tau-3,\tau^2+\tau-1,-\tau^2+4,-\tau-2)\). Every point in \(E(K)\) is twice another point in \(E(K)\). There is no class-number, norm-kernel, valuation, local-solubility or finiteness hypothesis. The coefficient-field interface is the original published interface, shared with the already-Proved Selmer arithmetic.
-- source:
--   User WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c. The original complete typed kernel and Lean AST closures are preserved. Already-Proved public rational and relative irreducibility, full ring-of-integers principality, exact supported Selmer cardinality 256, actual dyadic valuation-certificate inhabitation, normalized cubic unique root and non-square candidate certificates supply checked bridges. One coherent original coefficient/relative/ambient definition family avoids duplicate declarations in later alternative field-data packages. The named downstream consumer is the unchanged full rational genus-two exclusion for order18. All final campaign statements, coefficients and Apache-2.0 attribution remain unchanged. No custom axioms, resource strengthening or proof placeholders in the uploaded source.

import Mathlib
import Definitions.Def_MazurTransfer_Order18CoefficientFields

theorem MazurTransfer.order18_original_quotient_doubling_surjective : Function.Surjective (nsmulAddMonoidHom (α := MazurTorsion.XOneEighteenRealCubicQuotient.quotientCurve.toAffine.Point) 2) := by sorry
