-- Prove2me | Theorems.Thm_OAI_PiExponent_exists_successive_approximations
-- name    : OAI.PiExponent.exists_successive_approximations
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-09T10:33:15.787966+00:00
-- url     : https://prove2.me/theorems/4aba3255-1221-4afe-8855-017030ee3311
-- title:
--   Successive rational approximations with increasing logarithmic weights
-- statement:
--   Let $\nu>0$ and let $T$ map finite lists of real numbers to real numbers. Assume that approximations to $\pi$ with exponent $\nu$ exist above every natural denominator threshold. Then there are integer numerators $p_n$ and natural denominators $q_n$ such that, for every $n$,
--
--   $$2\le q_n,\quad p_n\ne0,\quad |\pi-p_n/q_n|\le q_n^{-\nu},\quad 1\le\lceil\log q_n\rceil,\quad T([\lceil\log q_{n-1}\rceil,\ldots,\lceil\log q_0\rceil])<\lceil\log q_n\rceil. $$
--
--   The list is empty when $n=0$. The uniform approximation premise is assumed; the theorem does not assert it unconditionally for $\pi$.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/SuccessiveApproximations.lean#L8-L55

import Lean
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic
import Theorems.Thm_OAI_PiExponent_exists_large_log_approximation

section



namespace OAI

namespace PiExponent



















end PiExponent

end OAI

end
section
open OAI OAI.PiExponent


open Lean Meta in
run_meta do
  let requests : Array (String × Lean.Name × String) := #[]
  let env ← Lean.getEnv
  let mut rows : Array Lean.Json := #[]
  let mut actualNames : Array Lean.Name := #[]
  for (sourceName, userName, expectedKind) in requests do
    let mut candidates : Array Lean.Name := #[]
    for (actualName, _) in env.constants.toList do
      if Lean.privateToUserName? actualName == some userName then
        if (env.getModuleIdxFor? actualName).isNone then
          candidates := candidates.push actualName
    unless candidates.size == 1 do
      throwError "Expected one OwnModule private binding for {userName}, found {candidates.size}"
    let actualName := candidates[0]!
    let some ci := env.find? actualName | throwError "Missing recovered private declaration"
    let (kind, value, safety) ← match ci with
      | .thmInfo t => pure ("theorem", t.value, Lean.Json.null)
      | .defnInfo d => pure ("def", d.value, Lean.toJson (reprStr d.safety))
      | _ => throwError "Recovered private CI is neither theorem nor definition"
    unless kind == expectedKind do
      throwError "Recovered private CI kind differs from source Graph: {actualName}"
    if ci.type.hasMVar || ci.type.hasFVar || ci.type.hasLooseBVars ||
        value.hasMVar || value.hasFVar || value.hasLooseBVars then
      throwError "Recovered private CI type/value is not closed"
    let axioms ← Lean.collectAxioms actualName
    unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
      throwError "Private helper has nonstandard axioms: {actualName}"
    actualNames := actualNames.push actualName
    rows := rows.push <| Lean.Json.mkObj [
      ("sourceGraphName", Lean.toJson sourceName),
      ("nodeGeneratedName", Lean.toJson userName.toString),
      ("actualKernelName", Lean.toJson actualName.toString),
      ("kind", Lean.toJson kind), ("safety", safety),
      ("ownerKind", Lean.toJson "OwnModule"),
      ("ownModule", Lean.toJson env.mainModule.toString),
      ("moduleIndexIsNone", Lean.toJson true),
      ("levelParams", Lean.toJson (ci.levelParams.map Lean.Name.toString)),
      ("typeRefs", Lean.toJson (ci.type.getUsedConstants.map Lean.Name.toString)),
      ("valueRefs", Lean.toJson (value.getUsedConstants.map Lean.Name.toString)),
      ("snapshotValueRequired", Lean.toJson (kind == "def")),
      ("axioms", Lean.toJson (axioms.map Lean.Name.toString))]
  IO.println ("PI_ISOLATED_PRIVATE_MAP " ++ (Lean.Json.mkObj [
    ("artifact", Lean.toJson "Thm"),
    ("ownModule", Lean.toJson env.mainModule.toString),
    ("rows", Lean.Json.arr rows)]).compress)

theorem OAI.PiExponent.exists_successive_approximations
    (nu : ℝ) (hnu : 0 < nu)
    (hbad : ∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
      Q ≤ q ∧ |Real.pi - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu))
    (T : List ℝ → ℝ) :
    ∃ p : ℕ → ℤ, ∃ q : ℕ → ℕ, ∀ n,
      2 ≤ q n ∧ p n ≠ 0 ∧
      |Real.pi - (p n : ℝ) / q n| ≤ (q n : ℝ) ^ (-nu) ∧
      1 ≤ Nat.ceil (Real.log (q n)) ∧
      T (((List.range n).reverse).map
        (fun i => ((Nat.ceil (Real.log (q i))) : ℝ))) <
          ((Nat.ceil (Real.log (q n))) : ℝ) := by sorry

end
