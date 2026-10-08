-- Prove2me | Theorems.Thm_MazurTransfer_order27_aggregate_numerator_one
-- name    : MazurTransfer.order27_aggregate_numerator_one
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T15:08:13.646867+00:00
-- url     : https://prove2.me/theorems/c641109b-5def-4ee8-94c3-753b3c1fda7f
-- title:
--   Order-27 kernel-cubic numerator: one
-- statement:
--   Let $f,\xi\in\mathbb Q$ satisfy the fixed trisection equation $T(f,\xi)=0$. The displayed term of the kernel-cubic numerator equals the displayed complete sum of fixed polynomial remainder blocks. This is the full original tl_mnum₁ identity, with its original hypotheses and coefficient functions. The downstream consumer combines the four numerator terms and their zero sum to obtain $M(f,N(f,\xi)/D(f,\xi))=0$ when $D(f,\xi)\ne0$. No rational-point existence or torsion exclusion is assumed.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Full signatures extracted using Lean signature AST ranges; proof commands retained by kernel dependencies and resolved references. This is an exact split of the terminal timed-out kernel coordinate verification, preserving the original hypotheses and conclusion. Original Apache-2.0 file headers retained.

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData1
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData2
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData3
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData4
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData5

open MazurTorsion.Kubert

theorem MazurTransfer.order27_aggregate_numerator_one :
(∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) ^ 3 =
      (((((((((tlNCbP0c0 f ξ + tlNCbP0c1 f ξ) + (tlNCbP0c2 f ξ + tlNCbP0c3 f ξ)) + ((tlNCbP0c4 f ξ
        + tlNCbP0c5 f ξ) + (tlNCbP0c6 f ξ + tlNCbP0c7 f ξ))) + (((tlNCbP0c8 f ξ + tlNCbP0c9 f ξ) +
        (tlNCbP0c10 f ξ + tlNCbP1c0 f ξ)) + ((tlNCbP1c1 f ξ + tlNCbP1c2 f ξ) + (tlNCbP1c3 f ξ +
        tlNCbP1c4 f ξ)))) + ((((tlNCbP1c5 f ξ + tlNCbP1c6 f ξ) + (tlNCbP1c7 f ξ + tlNCbP1c8 f ξ))
        + ((tlNCbP1c9 f ξ + tlNCbP1c10 f ξ) + (tlNCbP1c11 f ξ + tlNCbP1c12 f ξ))) + (((tlNCbP2c0 f
        ξ + tlNCbP2c1 f ξ) + (tlNCbP2c2 f ξ + tlNCbP2c3 f ξ)) + ((tlNCbP2c4 f ξ + tlNCbP2c5 f ξ) +
        (tlNCbP2c6 f ξ + tlNCbP2c7 f ξ))))) + (((((tlNCbP2c8 f ξ + tlNCbP2c9 f ξ) + (tlNCbP2c10 f
        ξ + tlNCbP2c11 f ξ)) + ((tlNCbP2c12 f ξ + tlNCbP2c13 f ξ) + (tlNCbP2c14 f ξ + tlNCbP3c0 f
        ξ))) + (((tlNCbP3c1 f ξ + tlNCbP3c2 f ξ) + (tlNCbP3c3 f ξ + tlNCbP3c4 f ξ)) + ((tlNCbP3c5
        f ξ + tlNCbP3c6 f ξ) + (tlNCbP3c7 f ξ + tlNCbP3c8 f ξ)))) + ((((tlNCbP3c9 f ξ + tlNCbP3c10
        f ξ) + (tlNCbP3c11 f ξ + tlNCbP3c12 f ξ)) + ((tlNCbP3c13 f ξ + tlNCbP3c14 f ξ) +
        (tlNCbP3c15 f ξ + tlNCbP4c0 f ξ))) + (((tlNCbP4c1 f ξ + tlNCbP4c2 f ξ) + (tlNCbP4c3 f ξ +
        tlNCbP4c4 f ξ)) + ((tlNCbP4c5 f ξ + tlNCbP4c6 f ξ) + (tlNCbP4c7 f ξ + tlNCbP4c8 f ξ))))))
        + ((((((tlNCbP4c9 f ξ + tlNCbP4c10 f ξ) + (tlNCbP4c11 f ξ + tlNCbP4c12 f ξ)) +
        ((tlNCbP4c13 f ξ + tlNCbP4c14 f ξ) + (tlNCbP4c15 f ξ + tlNCbP4c16 f ξ))) + (((tlNCbP5c0 f
        ξ + tlNCbP5c1 f ξ) + (tlNCbP5c2 f ξ + tlNCbP5c3 f ξ)) + ((tlNCbP5c4 f ξ + tlNCbP5c5 f ξ) +
        (tlNCbP5c6 f ξ + tlNCbP5c7 f ξ)))) + ((((tlNCbP5c8 f ξ + tlNCbP5c9 f ξ) + (tlNCbP5c10 f ξ
        + tlNCbP5c11 f ξ)) + ((tlNCbP5c12 f ξ + tlNCbP5c13 f ξ) + (tlNCbP5c14 f ξ + tlNCbP5c15 f
        ξ))) + (((tlNCbP5c16 f ξ + tlNCbP5c17 f ξ) + (tlNCbP6c0 f ξ + tlNCbP6c1 f ξ)) +
        ((tlNCbP6c2 f ξ + tlNCbP6c3 f ξ) + (tlNCbP6c4 f ξ + tlNCbP6c5 f ξ))))) + (((((tlNCbP6c6 f
        ξ + tlNCbP6c7 f ξ) + (tlNCbP6c8 f ξ + tlNCbP6c9 f ξ)) + ((tlNCbP6c10 f ξ + tlNCbP6c11 f ξ)
        + (tlNCbP6c12 f ξ + tlNCbP6c13 f ξ))) + (((tlNCbP6c14 f ξ + tlNCbP6c15 f ξ) + (tlNCbP6c16
        f ξ + tlNCbP6c17 f ξ)) + ((tlNCbP7c0 f ξ + tlNCbP7c1 f ξ) + (tlNCbP7c2 f ξ + tlNCbP7c3 f
        ξ)))) + ((((tlNCbP7c4 f ξ + tlNCbP7c5 f ξ) + (tlNCbP7c6 f ξ + tlNCbP7c7 f ξ)) +
        ((tlNCbP7c8 f ξ + tlNCbP7c9 f ξ) + (tlNCbP7c10 f ξ + tlNCbP7c11 f ξ))) + (((tlNCbP7c12 f ξ
        + tlNCbP7c13 f ξ) + (tlNCbP7c14 f ξ + tlNCbP7c15 f ξ)) + ((tlNCbP7c16 f ξ + tlNCbP7c17 f
        ξ) + (tlNCbP7c18 f ξ + tlNCbP8c0 f ξ))))))) + (((((((tlNCbP8c1 f ξ + tlNCbP8c2 f ξ) +
        (tlNCbP8c3 f ξ + tlNCbP8c4 f ξ)) + ((tlNCbP8c5 f ξ + tlNCbP8c6 f ξ) + (tlNCbP8c7 f ξ +
        tlNCbP8c8 f ξ))) + (((tlNCbP8c9 f ξ + tlNCbP8c10 f ξ) + (tlNCbP9c0 f ξ + tlNCbP9c1 f ξ)) +
        ((tlNCbP9c2 f ξ + tlNCbP9c3 f ξ) + (tlNCbP9c4 f ξ + tlNCbP9c5 f ξ)))) + ((((tlNCbP9c6 f ξ
        + tlNCbP9c7 f ξ) + (tlNCbP9c8 f ξ + tlNCbP9c9 f ξ)) + ((tlNCbP9c10 f ξ + tlNCbP9c11 f ξ) +
        (tlNCbP9c12 f ξ + tlNCbP10c0 f ξ))) + (((tlNCbP10c1 f ξ + tlNCbP10c2 f ξ) + (tlNCbP10c3 f
        ξ + tlNCbP10c4 f ξ)) + ((tlNCbP10c5 f ξ + tlNCbP10c6 f ξ) + (tlNCbP10c7 f ξ + tlNCbP10c8 f
        ξ))))) + (((((tlNCbP10c9 f ξ + tlNCbP10c10 f ξ) + (tlNCbP10c11 f ξ + tlNCbP10c12 f ξ)) +
        ((tlNCbP10c13 f ξ + tlNCbP11c0 f ξ) + (tlNCbP11c1 f ξ + tlNCbP11c2 f ξ))) + (((tlNCbP11c3
        f ξ + tlNCbP11c4 f ξ) + (tlNCbP11c5 f ξ + tlNCbP11c6 f ξ)) + ((tlNCbP11c7 f ξ + tlNCbP11c8
        f ξ) + (tlNCbP11c9 f ξ + tlNCbP11c10 f ξ)))) + ((((tlNCbP11c11 f ξ + tlNCbP11c12 f ξ) +
        (tlNCbP11c13 f ξ + tlNCbP11c14 f ξ)) + ((tlNCbP12c0 f ξ + tlNCbP12c1 f ξ) + (tlNCbP12c2 f
        ξ + tlNCbP12c3 f ξ))) + (((tlNCbP12c4 f ξ + tlNCbP12c5 f ξ) + (tlNCbP12c6 f ξ + tlNCbP12c7
        f ξ)) + ((tlNCbP12c8 f ξ + tlNCbP12c9 f ξ) + (tlNCbP12c10 f ξ + tlNCbP12c11 f ξ)))))) +
        ((((((tlNCbP12c12 f ξ + tlNCbP12c13 f ξ) + (tlNCbP12c14 f ξ + tlNCbP12c15 f ξ)) +
        ((tlNCbP13c0 f ξ + tlNCbP13c1 f ξ) + (tlNCbP13c2 f ξ + tlNCbP13c3 f ξ))) + (((tlNCbP13c4 f
        ξ + tlNCbP13c5 f ξ) + (tlNCbP13c6 f ξ + tlNCbP13c7 f ξ)) + ((tlNCbP13c8 f ξ + tlNCbP13c9 f
        ξ) + (tlNCbP13c10 f ξ + tlNCbP13c11 f ξ)))) + ((((tlNCbP13c12 f ξ + tlNCbP13c13 f ξ) +
        (tlNCbP13c14 f ξ + tlNCbP13c15 f ξ)) + ((tlNCbP13c16 f ξ + tlNCbP13c17 f ξ) + (tlNCbP14c0
        f ξ + tlNCbP14c1 f ξ))) + (((tlNCbP14c2 f ξ + tlNCbP14c3 f ξ) + (tlNCbP14c4 f ξ +
        tlNCbP14c5 f ξ)) + ((tlNCbP14c6 f ξ + tlNCbP14c7 f ξ) + (tlNCbP14c8 f ξ + tlNCbP14c9 f
        ξ))))) + (((((tlNCbP14c10 f ξ + tlNCbP14c11 f ξ) + (tlNCbP14c12 f ξ + tlNCbP14c13 f ξ)) +
        ((tlNCbP14c14 f ξ + tlNCbP14c15 f ξ) + (tlNCbP14c16 f ξ + tlNCbP14c17 f ξ))) +
        (((tlNCbP15c0 f + tlNCbP15c1 f ξ) + (tlNCbP15c2 f ξ + tlNCbP15c3 f ξ)) + ((tlNCbP15c4 f ξ
        + tlNCbP15c5 f ξ) + (tlNCbP15c6 f ξ + tlNCbP15c7 f ξ)))) + ((((tlNCbP15c8 f ξ + tlNCbP15c9
        f ξ) + (tlNCbP15c10 f ξ + tlNCbP15c11 f ξ)) + ((tlNCbP15c12 f ξ + tlNCbP15c13 f ξ) +
        (tlNCbP15c14 f ξ + tlNCbP15c15 f ξ))) + (((tlNCbP15c16 f ξ + tlNCbP15c17 f ξ) +
        (tlNCbP15c18 f ξ + tlNCbP16c0 f ξ)) + ((tlNCbP16c1 f ξ + tlNCbP16c2 f ξ) + (tlNCbP16c3 f ξ
        + tlNCbP16c4 f ξ)))))))) + ((((((((tlNCbP16c5 f ξ + tlNCbP16c6 f ξ) + (tlNCbP16c7 f ξ +
        tlNCbP16c8 f ξ)) + ((tlNCbP16c9 f ξ + tlNCbP16c10 f ξ) + (tlNCbP16c11 f ξ + tlNCbP16c12 f
        ξ))) + (((tlNCbP16c13 f ξ + tlNCbP16c14 f ξ) + (tlNCbP16c15 f ξ + tlNCbP16c16 f ξ)) +
        ((tlNCbP16c17 f ξ + tlNCbP16c18 f ξ) + (tlNCbP17c0 f ξ + tlNCbP17c1 f ξ)))) +
        ((((tlNCbP17c2 f ξ + tlNCbP17c3 f ξ) + (tlNCbP17c4 f ξ + tlNCbP17c5 f ξ)) + ((tlNCbP17c6 f
        ξ + tlNCbP17c7 f ξ) + (tlNCbP17c8 f ξ + tlNCbP17c9 f ξ))) + (((tlNCbP17c10 f ξ +
        tlNCbP17c11 f ξ) + (tlNCbP17c12 f ξ + tlNCbP17c13 f ξ)) + ((tlNCbP17c14 f ξ + tlNCbP17c15
        f ξ) + (tlNCbP17c16 f ξ + tlNCbP17c17 f ξ))))) + (((((tlNCbP17c18 f ξ + tlNCbP18c0 f ξ) +
        (tlNCbP18c1 f ξ + tlNCbP18c2 f ξ)) + ((tlNCbP18c3 f ξ + tlNCbP18c4 f ξ) + (tlNCbP18c5 f ξ
        + tlNCbP18c6 f ξ))) + (((tlNCbP18c7 f ξ + tlNCbP18c8 f ξ) + (tlNCbP18c9 f ξ + tlNCbP18c10
        f ξ)) + ((tlNCbP19c0 f ξ + tlNCbP19c1 f ξ) + (tlNCbP19c2 f ξ + tlNCbP19c3 f ξ)))) +
        ((((tlNCbP19c4 f ξ + tlNCbP19c5 f ξ) + (tlNCbP19c6 f ξ + tlNCbP19c7 f ξ)) + ((tlNCbP19c8 f
        ξ + tlNCbP19c9 f ξ) + (tlNCbP19c10 f ξ + tlNCbP19c11 f ξ))) + (((tlNCbP19c12 f ξ +
        tlNCbP20c0 f ξ) + (tlNCbP20c1 f ξ + tlNCbP20c2 f ξ)) + ((tlNCbP20c3 f ξ + tlNCbP20c4 f ξ)
        + (tlNCbP20c5 f ξ + tlNCbP20c6 f ξ)))))) + ((((((tlNCbP20c7 f ξ + tlNCbP20c8 f ξ) +
        (tlNCbP20c9 f ξ + tlNCbP20c10 f ξ)) + ((tlNCbP20c11 f ξ + tlNCbP20c12 f ξ) + (tlNCbP20c13
        f ξ + tlNCbP21c0 f ξ))) + (((tlNCbP21c1 f ξ + tlNCbP21c2 f ξ) + (tlNCbP21c3 f ξ +
        tlNCbP21c4 f ξ)) + ((tlNCbP21c5 f ξ + tlNCbP21c6 f ξ) + (tlNCbP21c7 f ξ + tlNCbP21c8 f
        ξ)))) + ((((tlNCbP21c9 f ξ + tlNCbP21c10 f ξ) + (tlNCbP21c11 f ξ + tlNCbP21c12 f ξ)) +
        ((tlNCbP21c13 f ξ + tlNCbP21c14 f ξ) + (tlNCbP22c0 f ξ + tlNCbP22c1 f ξ))) + (((tlNCbP22c2
        f ξ + tlNCbP22c3 f ξ) + (tlNCbP22c4 f ξ + tlNCbP22c5 f ξ)) + ((tlNCbP22c6 f ξ + tlNCbP22c7
        f ξ) + (tlNCbP22c8 f ξ + tlNCbP22c9 f ξ))))) + (((((tlNCbP22c10 f ξ + tlNCbP22c11 f ξ) +
        (tlNCbP22c12 f ξ + tlNCbP22c13 f ξ)) + ((tlNCbP22c14 f ξ + tlNCbP22c15 f ξ) + (tlNCbP23c0
        f ξ + tlNCbP23c1 f ξ))) + (((tlNCbP23c2 f ξ + tlNCbP23c3 f ξ) + (tlNCbP23c4 f ξ +
        tlNCbP23c5 f ξ)) + ((tlNCbP23c6 f ξ + tlNCbP23c7 f ξ) + (tlNCbP23c8 f ξ + tlNCbP23c9 f
        ξ)))) + ((((tlNCbP23c10 f ξ + tlNCbP23c11 f ξ) + (tlNCbP23c12 f ξ + tlNCbP23c13 f ξ)) +
        ((tlNCbP23c14 f ξ + tlNCbP23c15 f ξ) + (tlNCbP23c16 f ξ + tlNCbP24c0 f ξ))) +
        (((tlNCbP24c1 f ξ + tlNCbP24c2 f ξ) + (tlNCbP24c3 f ξ + tlNCbP24c4 f ξ)) + ((tlNCbP24c5 f
        ξ + tlNCbP24c6 f ξ) + (tlNCbP24c7 f ξ + tlNCbP24c8 f ξ))))))) + (((((((tlNCbP24c9 f ξ +
        tlNCbP24c10 f ξ) + (tlNCbP24c11 f ξ + tlNCbP24c12 f ξ)) + ((tlNCbP24c13 f ξ + tlNCbP24c14
        f ξ) + (tlNCbP24c15 f ξ + tlNCbP24c16 f ξ))) + (((tlNCbP24c17 f ξ + tlNCbP25c0 f) +
        (tlNCbP25c1 f ξ + tlNCbP25c2 f ξ)) + ((tlNCbP25c3 f ξ + tlNCbP25c4 f ξ) + (tlNCbP25c5 f ξ
        + tlNCbP25c6 f ξ)))) + ((((tlNCbP25c7 f ξ + tlNCbP25c8 f ξ) + (tlNCbP25c9 f ξ +
        tlNCbP25c10 f ξ)) + ((tlNCbP25c11 f ξ + tlNCbP25c12 f ξ) + (tlNCbP25c13 f ξ + tlNCbP25c14
        f ξ))) + (((tlNCbP25c15 f ξ + tlNCbP25c16 f ξ) + (tlNCbP25c17 f ξ + tlNCbP25c18 f ξ)) +
        ((tlNCbP26c0 f ξ + tlNCbP26c1 f ξ) + (tlNCbP26c2 f ξ + tlNCbP26c3 f ξ))))) +
        (((((tlNCbP26c4 f ξ + tlNCbP26c5 f ξ) + (tlNCbP26c6 f ξ + tlNCbP26c7 f ξ)) + ((tlNCbP26c8
        f ξ + tlNCbP26c9 f ξ) + (tlNCbP26c10 f ξ + tlNCbP26c11 f ξ))) + (((tlNCbP26c12 f ξ +
        tlNCbP26c13 f ξ) + (tlNCbP26c14 f ξ + tlNCbP26c15 f ξ)) + ((tlNCbP26c16 f ξ + tlNCbP26c17
        f ξ) + (tlNCbP26c18 f ξ + tlNCbP27c0 f ξ)))) + ((((tlNCbP27c1 f ξ + tlNCbP27c2 f ξ) +
        (tlNCbP27c3 f ξ + tlNCbP27c4 f ξ)) + ((tlNCbP27c5 f ξ + tlNCbP27c6 f ξ) + (tlNCbP27c7 f ξ
        + tlNCbP27c8 f ξ))) + (((tlNCbP27c9 f ξ + tlNCbP27c10 f ξ) + (tlNCbP27c11 f ξ +
        tlNCbP27c12 f ξ)) + ((tlNCbP27c13 f ξ + tlNCbP27c14 f ξ) + (tlNCbP27c15 f ξ + tlNCbP27c16
        f ξ)))))) + ((((((tlNCbP27c17 f ξ + tlNCbP27c18 f ξ) + (tlNCbP28c0 f ξ + tlNCbP28c1 f ξ))
        + ((tlNCbP28c2 f ξ + tlNCbP28c3 f ξ) + (tlNCbP28c4 f ξ + tlNCbP28c5 f ξ))) + (((tlNCbP28c6
        f ξ + tlNCbP28c7 f ξ) + (tlNCbP28c8 f ξ + tlNCbP28c9 f ξ)) + ((tlNCbP28c10 f ξ +
        tlNCbP28c11 f ξ) + (tlNCbP28c12 f ξ + tlNCbP28c13 f ξ)))) + ((((tlNCbP28c14 f ξ +
        tlNCbP28c15 f ξ) + (tlNCbP28c16 f ξ + tlNCbP28c17 f ξ)) + ((tlNCbP28c18 f ξ + tlNCbP29c0 f
        ξ) + (tlNCbP29c1 f ξ + tlNCbP29c2 f ξ))) + (((tlNCbP29c3 f ξ + tlNCbP29c4 f ξ) +
        (tlNCbP29c5 f ξ + tlNCbP29c6 f ξ)) + ((tlNCbP29c7 f ξ + tlNCbP29c8 f ξ) + (tlNCbP29c9 f ξ
        + tlNCbP29c10 f ξ))))) + (((((tlNCbP30c0 f ξ + tlNCbP30c1 f ξ) + (tlNCbP30c2 f ξ +
        tlNCbP30c3 f ξ)) + ((tlNCbP30c4 f ξ + tlNCbP30c5 f ξ) + (tlNCbP30c6 f ξ + tlNCbP30c7 f
        ξ))) + (((tlNCbP30c8 f ξ + tlNCbP30c9 f ξ) + (tlNCbP30c10 f ξ + tlNCbP30c11 f ξ)) +
        ((tlNCbP30c12 f ξ + tlNCbP31c0 f ξ) + (tlNCbP31c1 f ξ + tlNCbP31c2 f ξ)))) +
        ((((tlNCbP31c3 f ξ + tlNCbP31c4 f ξ) + (tlNCbP31c5 f ξ + tlNCbP31c6 f ξ)) + ((tlNCbP31c7 f
        ξ + tlNCbP31c8 f ξ) + (tlNCbP31c9 f ξ + tlNCbP31c10 f ξ))) + (((tlNCbP31c11 f ξ +
        tlNCbP31c12 f ξ) + (tlNCbP31c13 f ξ + tlNCbP32c0 f ξ)) + ((tlNCbP32c1 f ξ + tlNCbP32c2 f
        ξ) + (tlNCbP32c3 f ξ + tlNCbP32c4 f ξ))))))))) + ((((((((tlNCbP32c5 f ξ + tlNCbP32c6 f ξ)
        + (tlNCbP32c7 f ξ + tlNCbP32c8 f ξ)) + ((tlNCbP32c9 f ξ + tlNCbP32c10 f ξ) + (tlNCbP32c11
        f ξ + tlNCbP32c12 f ξ))) + (((tlNCbP32c13 f ξ + tlNCbP32c14 f ξ) + (tlNCbP32c15 f ξ +
        tlNCbP33c0 f ξ)) + ((tlNCbP33c1 f ξ + tlNCbP33c2 f ξ) + (tlNCbP33c3 f ξ + tlNCbP33c4 f
        ξ)))) + ((((tlNCbP33c5 f ξ + tlNCbP33c6 f ξ) + (tlNCbP33c7 f ξ + tlNCbP33c8 f ξ)) +
        ((tlNCbP33c9 f ξ + tlNCbP33c10 f ξ) + (tlNCbP33c11 f ξ + tlNCbP33c12 f ξ))) +
        (((tlNCbP33c13 f ξ + tlNCbP33c14 f ξ) + (tlNCbP33c15 f ξ + tlNCbP33c16 f ξ)) +
        ((tlNCbP34c0 f ξ + tlNCbP34c1 f ξ) + (tlNCbP34c2 f ξ + tlNCbP34c3 f ξ))))) +
        (((((tlNCbP34c4 f ξ + tlNCbP34c5 f ξ) + (tlNCbP34c6 f ξ + tlNCbP34c7 f ξ)) + ((tlNCbP34c8
        f ξ + tlNCbP34c9 f ξ) + (tlNCbP34c10 f ξ + tlNCbP34c11 f ξ))) + (((tlNCbP34c12 f ξ +
        tlNCbP34c13 f ξ) + (tlNCbP34c14 f ξ + tlNCbP34c15 f ξ)) + ((tlNCbP34c16 f ξ + tlNCbP34c17
        f ξ) + (tlNCbP35c0 f ξ + tlNCbP35c1 f ξ)))) + ((((tlNCbP35c2 f ξ + tlNCbP35c3 f ξ) +
        (tlNCbP35c4 f ξ + tlNCbP35c5 f ξ)) + ((tlNCbP35c6 f ξ + tlNCbP35c7 f ξ) + (tlNCbP35c8 f ξ
        + tlNCbP35c9 f ξ))) + (((tlNCbP35c10 f ξ + tlNCbP35c11 f ξ) + (tlNCbP35c12 f ξ +
        tlNCbP35c13 f ξ)) + ((tlNCbP35c14 f ξ + tlNCbP35c15 f ξ) + (tlNCbP35c16 f ξ + tlNCbP35c17
        f ξ)))))) + ((((((tlNCbP36c0 f + tlNCbP36c1 f ξ) + (tlNCbP36c2 f ξ + tlNCbP36c3 f ξ)) +
        ((tlNCbP36c4 f ξ + tlNCbP36c5 f ξ) + (tlNCbP36c6 f ξ + tlNCbP36c7 f ξ))) + (((tlNCbP36c8 f
        ξ + tlNCbP36c9 f ξ) + (tlNCbP36c10 f ξ + tlNCbP36c11 f ξ)) + ((tlNCbP36c12 f ξ +
        tlNCbP36c13 f ξ) + (tlNCbP36c14 f ξ + tlNCbP36c15 f ξ)))) + ((((tlNCbP36c16 f ξ +
        tlNCbP36c17 f ξ) + (tlNCbP36c18 f ξ + tlNCbP37c0 f)) + ((tlNCbP37c1 f ξ + tlNCbP37c2 f ξ)
        + (tlNCbP37c3 f ξ + tlNCbP37c4 f ξ))) + (((tlNCbP37c5 f ξ + tlNCbP37c6 f ξ) + (tlNCbP37c7
        f ξ + tlNCbP37c8 f ξ)) + ((tlNCbP37c9 f ξ + tlNCbP37c10 f ξ) + (tlNCbP37c11 f ξ +
        tlNCbP37c12 f ξ))))) + (((((tlNCbP37c13 f ξ + tlNCbP37c14 f ξ) + (tlNCbP37c15 f ξ +
        tlNCbP37c16 f ξ)) + ((tlNCbP37c17 f ξ + tlNCbP37c18 f ξ) + (tlNCbP38c0 f + tlNCbP38c1 f
        ξ))) + (((tlNCbP38c2 f ξ + tlNCbP38c3 f ξ) + (tlNCbP38c4 f ξ + tlNCbP38c5 f ξ)) +
        ((tlNCbP38c6 f ξ + tlNCbP38c7 f ξ) + (tlNCbP38c8 f ξ + tlNCbP38c9 f ξ)))) +
        ((((tlNCbP38c10 f ξ + tlNCbP38c11 f ξ) + (tlNCbP38c12 f ξ + tlNCbP38c13 f ξ)) +
        ((tlNCbP38c14 f ξ + tlNCbP38c15 f ξ) + (tlNCbP38c16 f ξ + tlNCbP38c17 f ξ))) +
        (((tlNCbP38c18 f ξ + tlNCbP39c0 f) + (tlNCbP39c1 f ξ + tlNCbP39c2 f ξ)) + ((tlNCbP39c3 f ξ
        + tlNCbP39c4 f ξ) + (tlNCbP39c5 f ξ + tlNCbP39c6 f ξ))))))) + (((((tlNCbP39c7 f ξ +
        tlNCbP39c8 f ξ) + (tlNCbP39c9 f ξ + tlNCbP39c10 f ξ)) + ((tlNCbP39c11 f ξ + tlNCbP39c12 f
        ξ) + (tlNCbP39c13 f ξ + tlNCbP39c14 f ξ))) + (((tlNCbP39c15 f ξ + tlNCbP39c16 f ξ) +
        (tlNCbP39c17 f ξ + tlNCbP39c18 f ξ)) + ((tlNCbP40c0 f + tlNCbP40c1 f ξ) + (tlNCbP40c2 f ξ
        + tlNCbP40c3 f ξ)))) + ((((tlNCbP40c4 f ξ + tlNCbP40c5 f ξ) + (tlNCbP40c6 f ξ + tlNCbP40c7
        f ξ)) + ((tlNCbP40c8 f ξ + tlNCbP40c9 f ξ) + (tlNCbP40c10 f ξ + tlNCbP40c11 f ξ))) +
        (((tlNCbP40c12 f ξ + tlNCbP40c13 f ξ) + (tlNCbP40c14 f ξ + tlNCbP40c15 f ξ)) +
        ((tlNCbP40c16 f ξ + tlNCbP40c17 f ξ) + tlNCbP40c18 f ξ)))))) := by sorry
