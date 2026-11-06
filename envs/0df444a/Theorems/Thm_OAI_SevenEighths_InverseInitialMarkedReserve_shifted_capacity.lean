-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseInitialMarkedReserve_shifted_capacity
-- name    : OAI.SevenEighths.InverseInitialMarkedReserve.shifted_capacity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T23:02:15.790866+00:00
-- url     : https://prove2.me/theorems/c730cb16-59d7-4ac1-9af0-a6b3810b838b
-- title:
--   Inverse Initial Marked Reserve: shifted capacity
-- statement:
--   The Inverse Initial Marked Reserve construction uses the shifted capacity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Inversion/InitialMarkedReserve.lean#L20-L39
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Inversion/InitialMarkedReserve.lean#L20-L39

import Definitions.Def_OAI_NumberTheory_DirichletL_Endpoint
import Definitions.Def_OAI_NumberTheory_DirichletL_Inversion_InitialMarkedReserve
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseInitialMarkedReserve

theorem OAI.SevenEighths.InverseInitialMarkedReserve.shifted_capacity (ρ gap η r r' ell G:ℝ)
    (hρ:0<ρ)(hρmax:ρ≤1/4)(hgap:2*gap≤ρ)
    (hη:0<η)(hηmax:η≤1/7)(hr:0≤r)(hell:0≤ell)
    (_hG:0≤G)(hGmax:G≤ell)(hlo:r-η≤r')(hhi:r'≤r)
    (hfirst:r+2*ell<1)(hsecond:2*r+8*ell<3):
    0≤1+ρ ∧ 1+ρ≤2 ∧ -2≤r'+ell-2*G ∧
      r'+2*ell≤(1+ρ)-2*gap ∧
      2*r'+8*ell≤3*(1+ρ)-2*gap ∧
      r'+ell+7*η≤2:= by sorry
