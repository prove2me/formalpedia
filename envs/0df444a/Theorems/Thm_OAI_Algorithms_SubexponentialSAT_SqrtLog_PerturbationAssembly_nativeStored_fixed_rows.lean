-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_PerturbationAssembly_nativeStored_fixed_rows
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.nativeStored_fixed_rows
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:06:10.238417+00:00
-- url     : https://prove2.me/theorems/f62d06e1-bddb-42c2-91e1-88a90587f230
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.nativeStored_fixed_rows: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.nativeStored_fixed_rows` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PerturbationAssemblySourceStored.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PerturbationAssemblySourceStored.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly`, with `open SubexponentialSAT DensePolynomialProgram`, `open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing`, `open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram`, `open LayoutSourceRowsProgram`, `open scoped BigOperators`):
--
--   ```lean
--   theorem nativeStored_fixed_rows (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
--       (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
--       (cache : RingProgram.ScalarCache 3 t) (u J N n : ℕ) (hu : 0 < u) (hJ : 0 < J)
--       (theta : Coeff (baseWidth 3 t) d)
--       (rows : List (Fixed.Array (baseWidth 3 t) d N × Bool)) (hlen : rows.length=n)
--       (family : Fin n → Polynomial (a.O t)) (bits : Fin n → Bool)
--       (hrow : ∀ i : Fin rows.length,
--         PerturbationProgram.polynomial (RingProgram.modelRing t ht hd a M cache) rows[i].1.val =
--           family (Fin.cast hlen i))
--       (hbits : ∀ i : Fin rows.length, rows[i].2 = bits (Fin.cast hlen i)) :
--       castJet hlen (nativeStored t ht hd a M cache u J N hu hJ theta rows).denote =
--         Squarefree.canonical u J (Moments.incidenceJet family
--           ((RingProgram.modelRing t ht hd a M cache).decode theta)
--           (∑ v : Fin n, (family v).eval ((RingProgram.modelRing t ht hd a M cache).decode theta) *
--             (if bits v then 1 else 0)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RepresentedRing` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Support` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Jet`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Poly`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.ZJet`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.canonical` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.instCommMonoidSupportOfDecidableEq` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Moments.Stored.denote` (definitions bundle `OAIQ081S060` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationProgram.polynomial` (definitions bundle `OAIQ081S063` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Moments.incidenceJet` (definitions bundle `OAIQ081S076` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.castJet` (definitions bundle `OAIQ081S098` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Coeff`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.modelRing` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.Array` (definitions bundle `OAIQ081S100` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.nativeStored` (definitions bundle `OAIQ081S151` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableDenotation.low_payload_realizes` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PerturbationAssemblySourceStored.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.nativeStored_fixed_rows)

import Mathlib
import Definitions.Def_OAIQ081S151

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT DensePolynomialProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open LayoutSourceRowsProgram
open scoped BigOperators

theorem nativeStored_fixed_rows (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u J N n : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : Coeff (baseWidth 3 t) d)
    (rows : List (Fixed.Array (baseWidth 3 t) d N × Bool)) (hlen : rows.length=n)
    (family : Fin n → Polynomial (a.O t)) (bits : Fin n → Bool)
    (hrow : ∀ i : Fin rows.length,
      PerturbationProgram.polynomial (RingProgram.modelRing t ht hd a M cache) rows[i].1.val =
        family (Fin.cast hlen i))
    (hbits : ∀ i : Fin rows.length, rows[i].2 = bits (Fin.cast hlen i)) :
    castJet hlen (nativeStored t ht hd a M cache u J N hu hJ theta rows).denote =
      Squarefree.canonical u J (Moments.incidenceJet family
        ((RingProgram.modelRing t ht hd a M cache).decode theta)
        (∑ v : Fin n, (family v).eval ((RingProgram.modelRing t ht hd a M cache).decode theta) *
          (if bits v then 1 else 0))) := by
  sorry

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end
