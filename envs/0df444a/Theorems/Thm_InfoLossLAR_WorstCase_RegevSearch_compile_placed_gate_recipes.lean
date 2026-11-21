-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_compile_placed_gate_recipes
-- name    : InfoLossLAR.WorstCase.RegevSearch.compile_placed_gate_recipes
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T05:50:48.187352+00:00
-- url     : https://prove2.me/theorems/04533c3a-a4ae-47f7-8916-e5c5e7600f2f
-- title:
--   Compilation of polynomial-time gate recipes with a measured output register
-- statement:
--   A polynomial-time rule specifies a number of work wires, a number of output wires, and a sequence of native gate codes on each input. A length-dependent binary table is appended before interpreting this rule. There exists a circuit family that exactly reproduces the Born probabilities of every circuit matching the rule. Its measured word has the selected output register as a prefix. If the table is polynomial-time computable, the resulting measured family is uniform quantum polynomial time.
-- source:
--   InfoLossLAR formalization of the single-coefficient Gaussian reduction, coherent shared-pool Fourier sampling, https://prove2.me/theorems/23174e03-6b1d-4113-b6b9-4dab17fa850a

import Definitions.Def_InfoLossLAR_WorstCase_QPT
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime

set_option autoImplicit false
open scoped BigOperators Classical
open QAlgorithms QAlgorithms.Complexity OAI.MetricKMedian.Binary.Automatic

namespace InfoLossLAR.WorstCase.RegevSearch

theorem compile_placed_gate_recipes
    (plan : Str→(List Unit × List Unit) × List (ℕ × ℕ × ℕ)) (hp : Poly plan) (table : Str→Str) :
    ∃ H : MFamily, (PolyTimeComputable table → IsMQPT H) ∧ ∀ w : Str,
      let s := w ++ table (unary w.length)
      let h := (plan s).1.1.length
      let k := (plan s).1.2.length
      ∃ message : Bits (h+k) → Str,
        (∀ z, List.ofFn (fun i : Fin k => z (Fin.natAdd h i)) <+: message z) ∧
        ∀ (c : Layered (h+k)), (plan s).2 = c.flatten.map (fun g => match g with
          | .h i => (0,i.val,0)
          | .s i => (1,i.val,0)
          | .t i => (2,i.val,0)
          | .x i => (3,i.val,0)
          | .cnot i j _ => (4,i.val,j.val)) →
          ∀ E : Str→Prop, outputProb H w E =
            ∑ z, if E (message z) then ‖runLayered c (fun x => if x = (fun _ => false) then 1 else 0) z‖^2 else 0 := by sorry

end InfoLossLAR.WorstCase.RegevSearch
