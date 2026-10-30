-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryReconstruction_run_space_with_full_frame
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction.run_space_with_full_frame
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T02:18:58.816823+00:00
-- url     : https://prove2.me/theorems/cffc2130-9606-4267-b5aa-791a3bf9bed3
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction.run_space_with_full_frame: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction.run_space_with_full_frame` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryReconstruction.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryReconstruction.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction`, with `open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing OAI.Algorithms.SubexponentialSAT.SqrtLog`, `open DensePolynomialProgram LeafProgram`, `open LeafParametersProgram`):
--
--   ```lean
--   theorem run_space_with_full_frame (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
--       (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
--       (cache : RingProgram.ScalarCache 3 (m.val 33))
--       (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
--       (hp : LeafRingSetupProgram.Produced m hd M cache half e)
--       (a : Data) (hscratch : a.stacks 89 = [])
--       (hframe : ∀ i ∈ ringPorts,
--         a.stacks (i.castAdd 576) = e.stacks (i.castAdd 320))
--       (hnodes : a.stacks 256 = e.stacks 256)
--       (hQ : 0 < m.val 21) (hJ : 0 < m.val 42)
--       (hfield : m.val 21 < 3^(m.val 34))
--       (hexponent : (Circuit.result Serialization.code m).val 44 = 3^(m.val 34)-2)
--       (jets : Fin (m.val 21) → CRTLocalProgram.Model.Poly
--         (baseWidth 3 (m.val 33)) (m.val 34) (m.val 42))
--       (hjets : a.stacks 863 = (List.finRange (m.val 21)).flatMap
--         (fun i => Fixed.encode (jets i)))
--       (target : Polynomial ((IrreducibleSearch.data hd).O (m.val 33)))
--       (hdegree : target.natDegree < m.val 21 * m.val 42)
--       (hhas : Reconstruction.HasJets
--         (RingProgram.modelRing (m.val 33) ht hd (IrreducibleSearch.data hd) M cache)
--         (fun i : Fin (m.val 21) => RingNodeProgram.nodeCode (m.val 33) (m.val 34) (i.val+1))
--         (m.val 42) (fun i => (jets i).1) target)
--       (count multiplicity ambient : ℕ) (hcount : count ≤ multiplicity*2^ambient)
--       (hlarge : multiplicity*2^ambient < 3^(m.val 33))
--       (hconstant : target.eval 0 = (count : (IrreducibleSearch.data hd).O (m.val 33)))
--       (B S : ℕ) (ha : ∀ i, (a.stacks i).length ≤ B)
--       (hQsize : m.val 21 ≤ S) (hJsize : m.val 42 ≤ S) (htsize : m.val 33 ≤ S)
--       (hdsize : m.val 34 ≤ S) (hqsize : 3^(m.val 34) ≤ S)
--       (hmodsize : (a.stacks 194).length ≤ S) (hwidthsize : (a.stacks 202).length ≤ S)
--       (hcountsize : (DisjointReuse.binaryNat count).length ≤ B) :
--       ∃ steps out, steps+1 ≤ budget B S ∧ Eval command steps a out ∧
--         Trace program (steps+1) (a.withPC (some program.entry)) (out.withPC none) ∧
--         out.stacks 323 = DisjointReuse.binaryNat count ∧
--         out.stacks 863 = [] ∧
--         (∀ i, (out.stacks i).length ≤ B) ∧
--         (∀ i : Fin 896, 768 ≤ i.val → i ≠ 863 → out.stacks i = a.stacks i) ∧
--         out.stacks 320 = a.stacks 320 ∧ out.stacks 322 = a.stacks 322 ∧
--         (∀ i : Fin 896, 330 ≤ i.val → i.val < 768 → i ≠ 699 → out.stacks i = a.stacks i) ∧
--         (∀ i : Fin 896, i ∈ retainedPorts → out.stacks i = a.stacks i) ∧
--         (∀ i : Fin 40, 16 ≤ i.val → out.regs i = a.regs i) ∧
--         ∀ q z, q ≤ steps+1 → Trace program q (a.withPC (some program.entry)) z →
--           ∀ i, (z.stacks i).length ≤ 896*B+budget B S
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.Model` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.binaryNat` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction.retainedPorts` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction.ringPorts` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Data` (definitions bundle `OAIQ081S034` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Reconstruction.HasJets` (definitions bundle `OAIQ081S063` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.result` (definitions bundle `OAIQ081S067` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction.budget` (definitions bundle `OAIQ081S081` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Coeff`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.modelRing` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.Poly` (definitions bundle `OAIQ081S100` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction.Data` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.encode` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.data` (definitions bundle `OAIQ081S121` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingNodeProgram.nodeCode` (definitions bundle `OAIQ081S122` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization.code` (definitions bundle `OAIQ081S153` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Produced` (definitions bundle `OAIQ081S166` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction.command` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction.program` (definitions bundle `OAIQ081S178` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryReconstruction.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction.run_space_with_full_frame)

import Mathlib
import Definitions.Def_OAIQ081S166
import Definitions.Def_OAIQ081S178

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction

open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing OAI.Algorithms.SubexponentialSAT.SqrtLog
open DensePolynomialProgram LeafProgram
open LeafParametersProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem run_space_with_full_frame (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (a : Data) (hscratch : a.stacks 89 = [])
    (hframe : ∀ i ∈ ringPorts,
      a.stacks (i.castAdd 576) = e.stacks (i.castAdd 320))
    (hnodes : a.stacks 256 = e.stacks 256)
    (hQ : 0 < m.val 21) (hJ : 0 < m.val 42)
    (hfield : m.val 21 < 3^(m.val 34))
    (hexponent : (Circuit.result Serialization.code m).val 44 = 3^(m.val 34)-2)
    (jets : Fin (m.val 21) → CRTLocalProgram.Model.Poly
      (baseWidth 3 (m.val 33)) (m.val 34) (m.val 42))
    (hjets : a.stacks 863 = (List.finRange (m.val 21)).flatMap
      (fun i => Fixed.encode (jets i)))
    (target : Polynomial ((IrreducibleSearch.data hd).O (m.val 33)))
    (hdegree : target.natDegree < m.val 21 * m.val 42)
    (hhas : Reconstruction.HasJets
      (RingProgram.modelRing (m.val 33) ht hd (IrreducibleSearch.data hd) M cache)
      (fun i : Fin (m.val 21) => RingNodeProgram.nodeCode (m.val 33) (m.val 34) (i.val+1))
      (m.val 42) (fun i => (jets i).1) target)
    (count multiplicity ambient : ℕ) (hcount : count ≤ multiplicity*2^ambient)
    (hlarge : multiplicity*2^ambient < 3^(m.val 33))
    (hconstant : target.eval 0 = (count : (IrreducibleSearch.data hd).O (m.val 33)))
    (B S : ℕ) (ha : ∀ i, (a.stacks i).length ≤ B)
    (hQsize : m.val 21 ≤ S) (hJsize : m.val 42 ≤ S) (htsize : m.val 33 ≤ S)
    (hdsize : m.val 34 ≤ S) (hqsize : 3^(m.val 34) ≤ S)
    (hmodsize : (a.stacks 194).length ≤ S) (hwidthsize : (a.stacks 202).length ≤ S)
    (hcountsize : (DisjointReuse.binaryNat count).length ≤ B) :
    ∃ steps out, steps+1 ≤ budget B S ∧ Eval command steps a out ∧
      Trace program (steps+1) (a.withPC (some program.entry)) (out.withPC none) ∧
      out.stacks 323 = DisjointReuse.binaryNat count ∧
      out.stacks 863 = [] ∧
      (∀ i, (out.stacks i).length ≤ B) ∧
      (∀ i : Fin 896, 768 ≤ i.val → i ≠ 863 → out.stacks i = a.stacks i) ∧
      out.stacks 320 = a.stacks 320 ∧ out.stacks 322 = a.stacks 322 ∧
      (∀ i : Fin 896, 330 ≤ i.val → i.val < 768 → i ≠ 699 → out.stacks i = a.stacks i) ∧
      (∀ i : Fin 896, i ∈ retainedPorts → out.stacks i = a.stacks i) ∧
      (∀ i : Fin 40, 16 ≤ i.val → out.regs i = a.regs i) ∧
      ∀ q z, q ≤ steps+1 → Trace program q (a.withPC (some program.entry)) z →
        ∀ i, (z.stacks i).length ≤ 896*B+budget B S := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction
end
