-- Prove2me | Theorems.Thm_LevyExtrema_SBA_not_cpp_tfae
-- name    : LevyExtrema.SBA.not_cpp_tfae
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:40:23.891847+00:00
-- url     : https://prove2.me/theorems/15a2120f-c76b-4423-ba15-afc3eda7ef42
-- title:
--   §4, Assumption 2 — not compound Poisson with drift ⇔ $\mathbb P(X_t=x)=0$ for some ⇔ for all $t>0$
-- statement:
--   Let $X=(X_t)_{t\ge0}$ be a Lévy process with generating triplet $(\sigma^2,\nu,b)$ on a probability space $(\Omega,\mathcal F,\mathbb P)$. The following are equivalent:
--
--   1. $X$ is not compound Poisson with drift, i.e. $\sigma\ne0$ or $\nu(\mathbb R)=\infty$;
--   2. there is $t>0$ with $\mathbb P(X_t=x)=0$ for every $x\in\mathbb R$;
--   3. $\mathbb P(X_t=x)=0$ for every $x\in\mathbb R$ and every $t>0$ (Assumption 2).
--
--   This is the equivalence the paper takes from Doeblin's diffuseness lemma, together with its "for some (and hence all) $t>0$". It lets every later statement use either form of the standing assumption of Section 4.
--
--   Differences from the source:
--   - encoding: X is not compound Poisson with drift → ¬ IsCPPWithDrift Tr, i.e. ¬(σ = 0 ∧ ν(ℝ) < ∞); reason: a Lévy process is compound Poisson with drift exactly when σ = 0 and ν is finite; same instances
--   - encoding: Lévy process X (paths in D[0,T], X_0 = 0) → IsLevyWith P X Tr: every path càdlàg and X_0 = 0 for every ω; reason: the paper's convention that paths lie in D[0,T] (p.18); a Lévy process has a càdlàg modification with X_0 = 0
-- source:
--   González Cázares, Mijatović, Uribe Bravo, Geometrically Convergent Simulation of the Extrema of Lévy Processes, arXiv:1810.11039v3, §4, p. 17 (paragraph before and statement of Assumption 2)

import Mathlib
import Definitions.Def_SingCtrlLevy_Barrier_Levy
import Definitions.Def_LevyExtrema_SBA_IsCPPWithDrift
import Definitions.Def_LevyExtrema_SBA_Assumption2

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LevyExtrema.SBA

open SingCtrlLevy.Barrier

/-- **§4 preamble and Assumption 2: not compound Poisson with drift ⇔ atomless marginals.**
González Cázares, Mijatović, Uribe Bravo, *Geometrically Convergent Simulation of the Extrema of
Lévy Processes*, arXiv:1810.11039v3, §4, p. 17: "Let X = (X_t)_{t≥0} be a Lévy process, which we
assume not to be compound Poisson with drift. By Doeblin's diffuseness lemma [Kal02, Lem. 13.22],
this is equivalent to the following requirement … Assumption 2. P(X_t = x) = 0 for all x ∈ R and
for some (and hence all) t > 0."

For a Lévy process `X` with generating triplet `Tr`, the following are equivalent:
(1) `X` is not compound Poisson with drift; (2) `P(X_t = x) = 0` for all `x` for some `t > 0`;
(3) the same for all `t > 0` (`Assumption2`).

**Formalization Note.** "Compound Poisson with drift" is read on the triplet
(`IsCPPWithDrift`: σ = 0 and ν(ℝ) < ∞). -/
theorem not_cpp_tfae {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (Tr : Triplet) (hX : IsLevyWith P X Tr) :
    List.TFAE [¬ IsCPPWithDrift Tr,
      ∃ t : ℝ≥0, 0 < t ∧ ∀ x : ℝ, P {ω | X t ω = x} = 0,
      Assumption2 P X] := by sorry

end LevyExtrema.SBA
