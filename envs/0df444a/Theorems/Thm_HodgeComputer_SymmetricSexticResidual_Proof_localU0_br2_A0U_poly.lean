-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localU0_br2_A0U_poly
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.localU0_br2_A0U_poly
-- status  : Open
-- author  : @benediamond
-- created : 2026-11-24T13:19:35.075096+00:00
-- url     : https://prove2.me/theorems/cfd6c239-db04-49ee-bce0-b804cca1c114
-- title:
--   Pure-field cleared polynomial identity for the Branch-2 dual jet of $A_{0U}$
-- statement:
--   Proves the division-free dual-number polynomial identity expressing the cleared $A_{0U, 12}$ linear combination at $Z_2$ over any characteristic-zero field $F$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueU0.lean#L3380-L3530

import Definitions.Def_HodgeComputerFormal_LaurentJets
set_option autoImplicit false

theorem HodgeComputer.SymmetricSexticResidual.Proof.localU0_br2_A0U_poly :
    ∀ {F : Type} [Field F] [CharZero F] (S Q T : F),
      let B := T - 3
      let A := 5 * S - 9 * Q
      let d_ab := 6 * S * B
      let Q_quad := 11943020 * S ^ 2 - 876486 * S * Q + 8382500 * S * T +
        5029500 * Q * T - 14837025 * S - 33647355 * Q
      let m_sc : Fin 10 → QuadraticCovers.Dual F := fun mi =>
        let a_s : QuadraticCovers.Dual F := ⟨6 * S ^ 2, 6 * S * B⟩
        let b_s : QuadraticCovers.Dual F := ⟨6 * S * Q, (5 * S - 3 * Q) * B⟩
        let ξS_s : QuadraticCovers.Dual F := ⟨-18 * S ^ 2, -6 * S * B * T⟩
        let ξQ_s : QuadraticCovers.Dual F := ⟨-18 * S * Q, -(5 * S - 3 * Q) * B * T⟩
        let dHS_v := fun s q : QuadraticCovers.Dual F => QuadraticCovers.Dual.C (-(25 / 243 : F)) * (5 * s - 9 * q) * (15 * s - 9 * q)
        let dHS_e := fun s q : QuadraticCovers.Dual F =>
          QuadraticCovers.Dual.C (143 / 81 : F) * s ^ 2 - QuadraticCovers.Dual.C (184 / 27 : F) * s * q + QuadraticCovers.Dual.C (52 / 9 : F) * q ^ 2
        let dHQ_v := fun s q : QuadraticCovers.Dual F => QuadraticCovers.Dual.C (50 / 27 : F) * s * (5 * s - 9 * q)
        let dHQ_e := fun (s q : QuadraticCovers.Dual F) (v0 : F) =>
          QuadraticCovers.Dual.C (-(92 / 27 : F)) * s ^ 2 + QuadraticCovers.Dual.C (104 / 9 : F) * s * q - QuadraticCovers.Dual.C (22 / 3 : F) * q ^ 2 +
            QuadraticCovers.Dual.C ((10 / 7 : F) * v0) * q + QuadraticCovers.Dual.C ((10 / 7 : F) * v0 ^ 2)
        let a2_v := dHS_v a_s b_s; let a2_e := dHS_e a_s b_s
        let a0_v := dHS_v ξS_s ξQ_s; let a0_e := dHS_e ξS_s ξQ_s
        let a1_v := dHS_v (a_s + ξS_s) (b_s + ξQ_s) - a2_v - a0_v
        let a1_e := dHS_e (a_s + ξS_s) (b_s + ξQ_s) - a2_e - a0_e
        let b2_v := dHQ_v a_s b_s; let b2_e := dHQ_e a_s b_s 0
        let b0_v := dHQ_v ξS_s ξQ_s; let b0_e := dHQ_e ξS_s ξQ_s d_ab
        let b1_v := dHQ_v (a_s + ξS_s) (b_s + ξQ_s) - b2_v - b0_v
        let b1_e := dHQ_e (a_s + ξS_s) (b_s + ξQ_s) 0 - b2_e - dHQ_e ξS_s ξQ_s 0 + QuadraticCovers.Dual.C ((10 / 7 : F) * d_ab) * b_s
        let d20_e := a2_v * b0_e + a2_e * b0_v - a0_v * b2_e - a0_e * b2_v
        let d21_e := a2_v * b1_e + a2_e * b1_v - a1_v * b2_e - a1_e * b2_v
        let d10_e := a1_v * b0_e + a1_e * b0_v - a0_v * b1_e - a0_e * b1_v
        let (m2, m1, m0) : QuadraticCovers.Dual F × QuadraticCovers.Dual F × QuadraticCovers.Dual F := match mi with
          | 0 => (a_s ^ 2, 2 * a_s * ξS_s, ξS_s ^ 2)
          | 1 => (a_s * b_s, a_s * ξQ_s + b_s * ξS_s, ξS_s * ξQ_s)
          | 2 => (b_s ^ 2, 2 * b_s * ξQ_s, ξQ_s ^ 2)
          | 3 => (QuadraticCovers.Dual.C d_ab * a_s, QuadraticCovers.Dual.C d_ab * ξS_s, 0)
          | 4 => (0, QuadraticCovers.Dual.C d_ab * a_s, QuadraticCovers.Dual.C d_ab * ξS_s)
          | 5 => (QuadraticCovers.Dual.C d_ab * b_s, QuadraticCovers.Dual.C d_ab * ξQ_s, 0)
          | 6 => (0, QuadraticCovers.Dual.C d_ab * b_s, QuadraticCovers.Dual.C d_ab * ξQ_s)
          | 7 => (QuadraticCovers.Dual.C (d_ab ^ 2), 0, 0)
          | 8 => (0, QuadraticCovers.Dual.C (d_ab ^ 2), 0)
          | 9 => (0, 0, QuadraticCovers.Dual.C (d_ab ^ 2))
        QuadraticCovers.Dual.C (1 / 16 : F) * (m2 * d10_e - m1 * d20_e + m0 * d21_e)
      QuadraticCovers.Dual.C (-(19708 / 1257375 : F)) * (5 * m_sc 0 - 9 * m_sc 1) +
        QuadraticCovers.Dual.C (1472 / 1257375 : F) * (5 * m_sc 1 - 9 * m_sc 2) -
        QuadraticCovers.Dual.C (16 / 729 : F) * (5 * m_sc 3 - 9 * m_sc 5) +
        QuadraticCovers.Dual.C (188 / 2025 : F) * (5 * m_sc 4 - 9 * m_sc 6) =
      QuadraticCovers.Dual.C (d_ab ^ 3) * ⟨(8248380 / 51331077 : F) * (5 * S - 3 * Q) * S ^ 3 * A ^ 2,
        -(2 / 51331077 : F) * B * S ^ 2 * A ^ 2 * Q_quad⟩ := by sorry
