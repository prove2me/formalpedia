-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_MovesV_preF_initR
-- name    : IntMul.Kappa.R8.Bit.Oppbank.MovesV_preF_initR
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T11:52:18.830272+00:00
-- url     : https://prove2.me/theorems/b0b5514f-3bb9-4093-bf13-ac9707eb0b7e
-- title:
--   Low-code prefix of the variant-R word is MovesV at bound 64251
-- statement:
--   # Low-code prefix of the variant-R word is a valid nested move
--
--   Let $W_{\mathrm{preF}}$ be the low-code prefix of the published variant-R stage-one word $W_{1F}$ (definition $\texttt{IntMul\_Kappa\_R8\_Data\_BitOppbankQHNetRecR}$), assembled from mix-forward, scatter, inject, and mix-inverse families, all at the low code $0$. Let $\mathrm{init}_R$ be the corresponding initial labelling: wire $w_X(t)$ carries the node code $c_{\mathrm{ND}}(t)=1773+t$, wire $w_T(c)$ carries $c_{\mathrm{ND}}(\mathrm{retN}(c))$ with densified $\mathrm{RETN}-1$, and every other wire is $0$. Write $\mathrm{genF}$ for the standard instruction generator, and write $\mathrm{ValidOn}$ / $\mathrm{MovesV}$ for the densified predicates at the flag-basis bound $64251$ (the Lab1 pack, not the stale generator bound $38286$).
--
--   Then
--
--   $$
--   \mathrm{ValidOn}(\mathrm{init}_R)
--   \;\wedge\;
--   \mathrm{MovesV}\bigl(\mathrm{genF}(\mathrm{init}_R,W_{\mathrm{preF}}).2\bigr)
--   \;\wedge\;
--   \mathrm{ValidOn}\bigl(\mathrm{genF}(\mathrm{init}_R,W_{\mathrm{preF}}).1\bigr).
--   $$
--
--   Every instruction in the prefix has code $0$, so each recorded overwrite has new code at most $1$ and is nested by the boundary clause of $\mathrm{nestOK}$. Codes remain strictly below $64251$ because the initial map is bounded and the prefix writes only $0$. This is a prefix certificate: it does not unfold $\mathrm{segsR}$ or claim $\mathrm{MovesV}$ of the full word $W_{1F}$.
--
--   **Formalization Note.** The proof is structural (membership in `mixF`/`scat`/`injo`/`mixI` and an induction on `genF`) and does not import `QHNet` or `QHNetRec`. The public generator is `Gen.genF`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: prefix MovesV/ValidOn for QHNetRecR.preF from initR (initH, RETN-1, wX t = cND t) at Lab.codeBound 64251. Not a full-word MovesV certificate.

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankGenF
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLab1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRecR
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace IntMul.Kappa.R8.Bit.Oppbank

/-- Variant-R stage-one initial map (`initH`): `wX t = cND t`,
`wT c = cND (retN c)` with densified `RETN-1`, all other wires `0`. -/
def initR (w : ℕ) : ℕ :=
  if w < v then QHNetRecR.cND w
  else if wAuxEnd ≤ w ∧ w < NL then QHNetRecR.cND (QHNetRecR.retN (w - wAuxEnd))
  else 0

/-- The low-code prefix `preF` of `QHNetRecR.W1F`, run from `initR`, is
`ValidOn` / `MovesV` at densified `codeBound = 64251`. This does not unfold
`segsR` or `W1F` and is not a full-word `MovesV` certificate. -/
theorem MovesV_preF_initR :
    Lab.ValidOn initR ∧
      Lab.MovesV (Gen.genF initR QHNetRecR.preF).2 ∧
        Lab.ValidOn (Gen.genF initR QHNetRecR.preF).1 := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
