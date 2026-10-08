-- Prove2me | Theorems.Thm_MazurTransfer_order_twenty_seven_legs_chain_impossible
-- name    : MazurTransfer.order_twenty_seven_legs_chain_impossible
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T12:15:04.31099+00:00
-- url     : https://prove2.me/theorems/67e27db0-d0cc-4fef-94b9-0978ebe7b64b
-- title:
--   No third rational leg in the order-27 tower
-- statement:
--   Let $f\in\mathbb Q$ satisfy $f\ne0,1$ and $f^3-6f^2+3f+1\ne0$. Put
--   $$a_2(f)=\frac{(f^3-6f^2+3f+1)^3}{f(f-1)(f^2-f+1)^3},$$
--   and let the Fricke-twisted $X_0(9)$ correspondence be
--   $$G(s,t)=s^2t^3+36s^2t^2+270s^2t-s^3+729st^2+26244st+531441t.$$
--   Then there is no $s_3\in\mathbb Q$ satisfying $G(a_2(f),s_3)=0$.
--
--   This rules out completing the first two rational hauptmodul legs of the nonsingular $X_1(9)$ family to a three-leg chain. The downstream consumer is the unconditional exclusion of rational points of exact order 27; that consumer must separately supply the third leg from a trisection point.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion/Kubert/OrderTwentySevenEndpoint.lean, legs_chain_impossible; MazurTorsion/NumberTheory/XZeroTwentySevenClassification.lean, spaceCurve_classification; MazurTorsion/NumberTheory/FermatCubicClassification.lean. Original polynomial certificates and Apache-2.0 headers retained. The cubic Fermat input is Mathlib fermatLastTheoremThree, with no assumption of the full FLT campaign.

import Mathlib
import Definitions.Def_MazurTransfer_OrderTwentySevenLegs

theorem MazurTransfer.order_twenty_seven_legs_chain_impossible
    (f : ℚ) (hf0 : f ≠ 0) (hf1 : f ≠ 1)
    (hK : f ^ 3 - 6 * f ^ 2 + 3 * f + 1 ≠ 0) (s3 : ℚ)
    (h2 : MazurTorsion.Kubert.orderNineG9F
      (MazurTorsion.Kubert.a2legN f / MazurTorsion.Kubert.a2legD f) s3 = 0) : False := by sorry
