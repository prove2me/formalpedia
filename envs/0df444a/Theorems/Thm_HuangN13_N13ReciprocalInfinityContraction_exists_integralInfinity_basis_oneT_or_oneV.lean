-- Prove2me | Theorems.Thm_HuangN13_N13ReciprocalInfinityContraction_exists_integralInfinity_basis_oneT_or_oneV
-- name    : HuangN13.N13ReciprocalInfinityContraction.exists_integralInfinity_basis_oneT_or_oneV
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T14:20:47.928326+00:00
-- url     : https://prove2.me/theorems/5353c686-b674-4331-b2a9-050865941e63
-- title:
--   exists integralInfinity basis oneT or oneV
-- statement:
--   Exact transplant of the original proof of MazurProof.N13ReciprocalInfinityContraction.exists_integralInfinity_basis_oneT_or_oneV from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit9 lines7701–7898, command SHA-256 5d79bf21c7593111d5fbb56dd4b52795d58a62dbc4d45f1d5912cc022c612a0d.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_ChooserSmallStatementCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_VerticalGraphStatementCore

set_option autoImplicit false
open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT

theorem HuangN13.N13ReciprocalInfinityContraction.exists_integralInfinity_basis_oneT_or_oneV
    (D : MazurProof.SexticMumford.Mumford MazurProof.N13ReciprocalInfinityContraction.Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (hfinite :
      Module.Finite MazurProof.N13ReciprocalInfinityContraction.R₂
        (MazurProof.N13ReciprocalInfinityContraction.InfinityRing ⧸ MazurProof.N13ReciprocalInfinityContraction.integralInfinityIdeal D hdeg h0)) :
    (∃ bT : Basis (Fin 2) MazurProof.N13ReciprocalInfinityContraction.R₂
        (MazurProof.N13ReciprocalInfinityContraction.InfinityRing ⧸ MazurProof.N13ReciprocalInfinityContraction.integralInfinityIdeal D hdeg h0),
      (bT : Fin 2 →
        MazurProof.N13ReciprocalInfinityContraction.InfinityRing ⧸ MazurProof.N13ReciprocalInfinityContraction.integralInfinityIdeal D hdeg h0) =
        MazurProof.N13FiniteFlatBasisLift.oneX
          (Ideal.Quotient.mk
            (MazurProof.N13ReciprocalInfinityContraction.integralInfinityIdeal D hdeg h0)
            MazurProof.N13IntegralInfinityChart.tClass)) ∨
      (∃ bV : Basis (Fin 2) MazurProof.N13ReciprocalInfinityContraction.R₂
        (MazurProof.N13ReciprocalInfinityContraction.InfinityRing ⧸ MazurProof.N13ReciprocalInfinityContraction.integralInfinityIdeal D hdeg h0),
      (bV : Fin 2 →
        MazurProof.N13ReciprocalInfinityContraction.InfinityRing ⧸ MazurProof.N13ReciprocalInfinityContraction.integralInfinityIdeal D hdeg h0) =
        MazurProof.N13FiniteFlatBasisLift.oneX
          (Ideal.Quotient.mk
            (MazurProof.N13ReciprocalInfinityContraction.integralInfinityIdeal D hdeg h0)
            MazurProof.N13IntegralInfinityChart.vClass)) := by sorry
