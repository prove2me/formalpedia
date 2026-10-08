-- Prove2me | Theorems.Thm_NetTraffic_OnOffStable_lemma_6
-- name    : NetTraffic.OnOffStable.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:14:55.089996+00:00
-- url     : https://prove2.me/theorems/d700004c-9026-4b08-a770-58cca5ce7fc2
-- title:
--   Lemma 6, p. 45 — [b(MT)]⁻¹(A₃ − EA₃) → 0 in probability
-- statement:
--   Under (2.1)–(2.2) and Slow Growth Condition 1, with $M=M(T)$ independent stationary ON/OFF sources, let
--   $$A_3=\sum_{m=1}^M\max\Bigl(0,\,T^{(m)}_{\xi^{(m)}_T-1}+X^{(m)}_{\xi^{(m)}_T}-T\Bigr)\mathbf 1_{[\xi^{(m)}_T\ge1]}$$
--   be the total overshoot beyond $T$ of the last ON-periods started in $[0,T]$. Then $A_3$ is integrable and, as $T\to\infty$,
--   $$[b(MT)]^{-1}\bigl(A_3-EA_3\bigr)\xrightarrow{P}0 .$$
--
--   Together with Lemma 3 this shows that only $A_2=\sum_m\sum_{k=1}^{\xi^{(m)}_T}X^{(m)}_k$ matters in the decomposition $A(T)=A_1+A_2-A_3$ of §5.2.
--
--   **Formalization Note.** Integrability of $A_3$ for every $T$ is stated as part of the conclusion, so that $EA_3$ is not the Bochner integral's junk value. The decomposition on p. 41 subtracts the $A_3$ sum; the Lean `A3` is that sum itself, as in Lemma 6.
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), p. 41 (definition of A₃) and p. 45, Lemma 6

import Mathlib
import Definitions.Def_NetTraffic_OnOffStable_Setting

namespace NetTraffic.OnOffStable

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics

theorem lemma_6
    {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon] [IsProbabilityMeasure Foff]
    {α αoff : ℝ} (hF : HeavyTails Fon Foff α αoff)
    {M : ℝ → ℕ} (hM : SourceCount M) (hC1 : Condition1 Fon M)
    {Ω : ℝ → Type*} [∀ T, MeasurableSpace (Ω T)] (P : ∀ T, Measure (Ω T))
    [∀ T, IsProbabilityMeasure (P T)] (src : ∀ T, ℕ → Source (Ω T))
    (hsrc : ∀ T, IsOnOffSuperposition (P T) Fon Foff (M T) (src T)) :
    (∀ T, Integrable (A3 (M T) (src T) T) (P T)) ∧
    NetTraffic.PoissonStable.TendstoInProbZero P (fun T ω =>
      (A3 (M T) (src T) T ω - (P T)[A3 (M T) (src T) T]) / NetTraffic.PoissonStable.b Fon ((M T : ℝ) * T)) := by sorry

end NetTraffic.OnOffStable
