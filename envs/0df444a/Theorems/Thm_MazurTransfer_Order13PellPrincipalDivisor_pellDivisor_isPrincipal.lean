-- Prove2me | Theorems.Thm_MazurTransfer_Order13PellPrincipalDivisor_pellDivisor_isPrincipal
-- name    : MazurTransfer.Order13PellPrincipalDivisor.pellDivisor_isPrincipal
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T14:29:43.223866+00:00
-- url     : https://prove2.me/theorems/2d938842-7792-4381-9fd4-9317b53b1a7c
-- title:
--   The explicit degree-nineteen difference of the two actual infinity places is principal
-- statement:
--   On the literal order-13 curve over $\mathbb Q$, let $v_+$ and $v_-$ be the canonical degree-one places of its specified infinity sections. The original two-point divisor $$D=19[v_-]-19[v_+]$$ is principal. This supplies the annihilation by nineteen of the original infinity divisor class in arithmetic $\operatorname{Pic}^0$.
-- source:
--   Original complete pellDivisor_isPrincipal statement and proof, with original pellDivisor_coefficient and pellFunction_ne_zero helper proofs, from MazurTheorem Order13PellPrincipalDivisor.lean, Apache-2.0, Vas and contributors. The explicit original Pell function witnesses the principal-divisor assertion. Public proved canonical infinity orders, global orders away from infinity and ordinary unit expression supply all dependencies. The complete original closed type is kernel-compared. Named downstream consumer: exact additive order nineteen of the actual infinity Picard class.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the exact two-point principal divisor of the explicit Pell
function in the actual rational scheme function field. Named downstream
consumer: nineteen annihilates the difference of the infinity Picard classes.
-/
import Definitions.Def_MazurTransfer_Order13PellPrincipalDivisorData
import Definitions.Def_MazurTransfer_Order13PellChartOverlapIdentities
import Theorems.Thm_MazurTransfer_Order13PellPrincipalDivisor_pellFunction_ord_away_infinity
import Theorems.Thm_MazurTransfer_Order13PellActualOrdinaryChart_pellFunction_eq_ordinaryPlus
noncomputable section
open MazurTransfer
open Order13PellPrincipalDivisor
open AlgebraicGeometry AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13IntegralSections Order13RationalSectionPicardInjection Order13ActualInfinityPlaceCenters
open Order13PellActualInfinityValuations
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

theorem MazurTransfer.Order13PellPrincipalDivisor.pellDivisor_isPrincipal : Divisor.IsPrincipal pellDivisor := by sorry
