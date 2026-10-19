-- Prove2me | Theorems.Thm_MazurTransfer_FiniteDivisorialPairingPerfectOfInjective_perfect_of_toHom_injective
-- name    : MazurTransfer.FiniteDivisorialPairingPerfectOfInjective.perfect_of_toHom_injective
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T08:20:50.146474+00:00
-- url     : https://prove2.me/theorems/c414425a-751e-4369-aa62-5b486a9a579a
-- title:
--   A finite divisorial pairing is perfect when its character map is injective
-- statement:
--   Let K and F be fields with a K algebra structure on F and the original principal-divisor package. Let n be a nonzero natural number and suppose the n-torsion of Pic0 K F is finite. For any original divisorial Weil pairing data e, if its character map e.toHom is injective, then e.Perfect holds. No algebraic closure or enough-roots-of-unity hypothesis is added. Named downstream consumer: perfection of the actual order-13 divisorial nineteen-pairing and the two individual norm-kernel ranks.
-- source:
--   MazurTheorem, FiniteDivisorialPairingPerfectOfInjective.lean, Apache-2.0. The two finite-character helper proofs are reused from official Anthropic FLT P2M/Sol/S_AddMonoidHom_natCard_ker_eq_natCard_ker_of_pairing_adjoint.lean at exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0. Original complete theorem and both helper types checked.

import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial
noncomputable section
open AlgebraicCurve

theorem MazurTransfer.FiniteDivisorialPairingPerfectOfInjective.perfect_of_toHom_injective {K F : Type*} [Field K] [Field F] [Algebra K F]
    [HasPrincipalDivisors K F] {n : ℕ} [NeZero n]
    [Finite (Pic0.torsion K F n)]
    (e : DivisorialWeilPairingData K F n)
    (hi : Function.Injective e.toHom) : e.Perfect := by sorry
