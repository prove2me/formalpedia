-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_ae_pi_snoc
-- name    : OAI.NoiselessRegression.ae_pi_snoc
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:34:57.360209+00:00
-- url     : https://prove2.me/theorems/55621fe9-59bc-4b49-a6bc-ca57b04d5826
-- title:
--   Almost-everywhere statements for appended product coordinates
-- statement:
--   Let $\nu$ be a measure and $P$ a measurable property of $(n+1)$-tuples. Then $P$ holds for $\nu^{\otimes(n+1)}$-almost every tuple if and only if, for $\nu^{\otimes n}$-almost every $v$, it holds for $\nu$-almost every $x$ at the tuple obtained by appending $x$ to $v$:
--   $$
--   \forall^{\mathrm{a.e.}}w\ P(w)\iff\forall^{\mathrm{a.e.}}v\ \forall^{\mathrm{a.e.}}x\ P(v,x).
--   $$
--
--   It is used to integrate over replicas one coordinate at a time.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/ReplicaMoments.lean#L97-L116

import Mathlib
import Definitions.Def_ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Gram__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments__ProjectionMoments

open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
universe u
variable {E : Type*} [MeasurableSpace E] {n : ℕ} (ν : Measure E) [SigmaFinite ν]

theorem OAI.NoiselessRegression.ae_pi_snoc {P : (Fin (n+1) → E) → Prop} (hP : MeasurableSet {v | P v}) :
    (∀ᵐ v ∂Measure.pi (fun _ => ν), P v) ↔
      ∀ᵐ v : Fin n → E ∂Measure.pi (fun _ => ν), ∀ᵐ x ∂ν, P (Fin.snoc v x) := by sorry
