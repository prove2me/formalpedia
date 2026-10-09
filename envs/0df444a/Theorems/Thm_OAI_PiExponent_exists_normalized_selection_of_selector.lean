-- Prove2me | Theorems.Thm_OAI_PiExponent_exists_normalized_selection_of_selector
-- name    : OAI.PiExponent.exists_normalized_selection_of_selector
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-09T11:02:18.038434+00:00
-- url     : https://prove2.me/theorems/70770615-f641-4c27-b499-56d5c6cd07dd
-- title:
--   Normalize a selector sequence and obtain product growth
-- statement:
--   Let $\nu,X,D\in\mathbb R$. Suppose that for every threshold rule $T$ on finite lists there are integer numerators $p_n$ and natural denominators $q_n$ such that, for every $n$, $q_n\ge2$, $p_n\ne0$, $|\pi-p_n/q_n|\le q_n^{-\nu}$, and the logarithmic ceiling weights satisfy $1\le\lceil\log q_n\rceil$ and exceed $T$ applied to the earlier weights in reverse order. Then there are sequences $p_n,q_n,x_n$ with $x_0=1$ and $x_{n+1}=\lceil\log q_n\rceil$ for which
--
--   $$x_i\ge1,\quad X<x_{n+1},\quad D\prod_{j<i}x_j<x_i\quad(i>0),$$
--
--   while every pair $(p_n,q_n)$ retains the same power-law approximation, nonzero-numerator, denominator, and positive-weight conditions. The selector hypothesis is part of the result. This normalization packages the uniform lower margin and multiplicative separation into a sequence that can be reused when later admissibility constraints depend on accumulated weights. No sign restrictions on $X$ or $D$ are required.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/SuccessiveApproximations.lean#L97-L132

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_SuccessiveApproximations
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

section



namespace OAI

namespace PiExponent











@[simp] theorem normalizedLogWeights_zero (q : ℕ → ℕ) :
    normalizedLogWeights q 0 = 1 := rfl

@[simp] theorem normalizedLogWeights_succ (q : ℕ → ℕ) (n : ℕ) :
    normalizedLogWeights q (n + 1) = (Nat.ceil (Real.log (q n)) : ℝ) := rfl

theorem reverse_logWeights_prod (q : ℕ → ℕ) (n : ℕ) :
    (((List.range n).reverse).map
      (fun i => (Nat.ceil (Real.log (q i)) : ℝ))).prod =
      ∏ j ∈ Finset.range (n + 1), normalizedLogWeights q j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.reverse_append]
    simp only [List.reverse_singleton, List.map_append, List.map_singleton,
      List.prod_append, List.prod_cons, List.prod_nil, mul_one]
    rw [Finset.prod_range_succ, ih, normalizedLogWeights_succ]
    exact mul_comm _ _





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

theorem OAI.PiExponent.exists_normalized_selection_of_selector
    (nu X D : ℝ)
    (hselect : ∀ T : List ℝ → ℝ,
      ∃ p : ℕ → ℤ, ∃ q : ℕ → ℕ, ∀ n,
        2 ≤ q n ∧ p n ≠ 0 ∧
        |Real.pi - (p n : ℝ) / q n| ≤ (q n : ℝ) ^ (-nu) ∧
        1 ≤ Nat.ceil (Real.log (q n)) ∧
        T (((List.range n).reverse).map
          (fun i => ((Nat.ceil (Real.log (q i))) : ℝ))) <
            ((Nat.ceil (Real.log (q n))) : ℝ)) :
    ∃ p : ℕ → ℤ, ∃ q : ℕ → ℕ, ∃ x : ℕ → ℝ,
      x 0 = 1 ∧
      (∀ n, x (n + 1) = (Nat.ceil (Real.log (q n)) : ℝ)) ∧
      (∀ n, 2 ≤ q n ∧ p n ≠ 0 ∧
        |Real.pi - (p n : ℝ) / q n| ≤ (q n : ℝ) ^ (-nu) ∧
        1 ≤ Nat.ceil (Real.log (q n)) ∧ X < x (n + 1)) ∧
      (∀ i, 1 ≤ x i) ∧
      (∀ i, 0 < i → D * (∏ j ∈ Finset.range i, x j) < x i) := by sorry

end
