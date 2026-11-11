-- Prove2me | Theorems.Thm_OAI_UniformKServer_UniformWrapper_all_reachable
-- name    : OAI.UniformKServer.UniformWrapper.all_reachable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:01:10.39266+00:00
-- url     : https://prove2.me/theorems/f406b466-f021-4d00-bad2-eb2d5612d175
-- title:
--   OAI.UniformKServer.UniformWrapper.all_reachable: intermediate lemma from OpenAI, Uniform computation of the squared-logarithmic k-server bound
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniformKServer.uniform_squared_logarithmic_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform computation of the squared-logarithmic k-server bound*, OpenAI Math Release, September 24, 2026, result family 110, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniformKServer.UniformWrapper.all_reachable` of [lean/OAI/Combinatorics/UniformKServer/WrapperReachable.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/UniformKServer/WrapperReachable.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniformKServer.UniformWrapper`, with `open TypedStack RawCertificate`, `open scoped Classical`):
--
--   ```lean
--    theorem all_reachable {n k : ℕ} (mult : ℕ) (hk : 0<k) (hkn : k≤n)
--       (v : Certificate) (hR : 0 < restart v)
--       (hT : rowsOK n k (UniformKServer.horizon k (cap v)) (bits v) (table v)=true)
--       (c : RuntimeCertificate.Cert) (hc : RuntimeCertificate.verify n k v c=true)
--       (delay : ℕ) (hd : 2^c.2≤delay) (a : CoreState mult)
--       (p : Prefix (uniform mult) a (ready (RuntimeCertificate.B k v)
--         (Encodable.encode (RawProgram.initial n k v)) BitTape.blank [] true) delay)
--       (d : RationalMetric n) (s : Configuration n k)
--       (hb : CoreRep (uniform mult) a (boot (machine mult) 64 1 d s))
--       (t : ℕ) (z : MachineState (machine mult)) (hz : Reachable (machine mult) 64 1 d s t z) :
--       Live (n:=n) (k:=k) mult v c delay p.state t z
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniformKServer.horizon`, `OAI.UniformKServer.FlatTM2.Local`, `OAI.UniformKServer.FlatTM2.Node`, `OAI.UniformKServer.LiteralPartrec.supp`, `OAI.UniformKServer.RawArithmetic.Q`, `OAI.UniformKServer.RawCertificate.Certificate`, `OAI.UniformKServer.RawCertificate.bits`, `OAI.UniformKServer.RawCertificate.cap`, `OAI.UniformKServer.RawCertificate.restart`, `OAI.UniformKServer.RawCertificate.rowsOK`, `OAI.UniformKServer.RawCertificate.table`, `OAI.UniformKServer.RawFilter.E`, `OAI.UniformKServer.RawFilter.F`, `OAI.UniformKServer.RuntimeCertificate.Cert`, `OAI.UniformKServer.TypedStack.CoreRep`, `OAI.UniformKServer.TypedStack.Prefix` and `OAI.UniformKServer.UniformWrapper.g` (definitions bundle `Q220Uk002` of this split); `OAI.UniformKServer.UniformWrapper.Control` (definitions bundle `Q220Uk003` of this split); `OAI.UniformKServer.ConstructorProgram.code`, `OAI.UniformKServer.LiteralVector.activeCode`, `OAI.UniformKServer.RawControl.S`, `OAI.UniformKServer.RawGlobal.S`, `OAI.UniformKServer.RawProgram.Payload`, `OAI.UniformKServer.RawProgram.initial`, `OAI.UniformKServer.RuntimeCertificate.B` and `OAI.UniformKServer.RuntimeCertificate.verify` (definitions bundle `Q220Uk005` of this split); `OAI.UniformKServer.UniformWrapper.Key` (definitions bundle `Q220Uk006` of this split); `OAI.UniformKServer.UniformWrapper.CoreState`, `OAI.UniformKServer.UniformWrapper.Live`, `OAI.UniformKServer.UniformWrapper.machine`, `OAI.UniformKServer.UniformWrapper.ready` and `OAI.UniformKServer.UniformWrapper.uniform` (definitions bundle `Q220Uk008` of this split); `OAI.UniformKServer.Configuration`, `OAI.UniformKServer.MachineState`, `OAI.UniformKServer.RationalMetric`, `OAI.UniformKServer.Reachable`, `OAI.UniformKServer.boot` and `OAI.UniformKServer.BitTape.blank` (the published bundle `Def_UniformKServer`).
--
--   **Used by.** The proof of `OAI.UniformKServer.uniform_squared_logarithmic_main` of this split imports it.
-- source:
--   OpenAI, Uniform computation of the squared-logarithmic k-server bound, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 110; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Uniform-computation-of-the-squared-logarithmic-k-server-bound-September-24-2026/Uniform-computation-of-the-squared-logarithmic-k-server-bound-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/UniformKServer/WrapperReachable.lean (declaration OAI.UniformKServer.UniformWrapper.all_reachable)

import Mathlib
import Definitions.Def_UniformKServer
import Definitions.Def_Q220Uk008

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.UniformWrapper
open TypedStack RawCertificate
open scoped Classical

 theorem all_reachable {n k : ℕ} (mult : ℕ) (hk : 0<k) (hkn : k≤n)
    (v : Certificate) (hR : 0 < restart v)
    (hT : rowsOK n k (UniformKServer.horizon k (cap v)) (bits v) (table v)=true)
    (c : RuntimeCertificate.Cert) (hc : RuntimeCertificate.verify n k v c=true)
    (delay : ℕ) (hd : 2^c.2≤delay) (a : CoreState mult)
    (p : Prefix (uniform mult) a (ready (RuntimeCertificate.B k v)
      (Encodable.encode (RawProgram.initial n k v)) BitTape.blank [] true) delay)
    (d : RationalMetric n) (s : Configuration n k)
    (hb : CoreRep (uniform mult) a (boot (machine mult) 64 1 d s))
    (t : ℕ) (z : MachineState (machine mult)) (hz : Reachable (machine mult) 64 1 d s t z) :
    Live (n:=n) (k:=k) mult v c delay p.state t z := by
  sorry

end UniformKServer.UniformWrapper

end

end OAI
end
