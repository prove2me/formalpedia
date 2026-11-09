-- Prove2me | Theorems.Thm_GirthBethe_Sharp_concave_information_data_processing
-- name    : GirthBethe.Sharp.concave_information_data_processing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T07:15:43.598825+00:00
-- url     : https://prove2.me/theorems/9a153946-d3eb-4c0c-bdee-6d2a383b85b8
-- title:
--   Lemma 2.7 — data processing for concave information gain
-- statement:
--   Let $U,Y,Z$ be finite random variables, with $U$ taking values in a finite set $\Omega$, and let $\Psi:\Delta(\Omega)\to\mathbb R$ be concave. Suppose $U$–$Y$–$Z$ is a Markov chain, i.e. $U$ and $Z$ are conditionally independent given $Y$:
--   $$P(U=a,Y=b,Z=c)\,P(Y=b)=P(U=a,Y=b)\,P(Y=b,Z=c)\quad\text{for all }a,b,c.$$
--   Then
--   $$I_\Psi(U;Y)\ \ge\ I_\Psi(U;Z)\ \ge\ 0 .$$
--
--   Applied with $\Psi=\Gamma$ it drives the permutation information inequality, Lemma 5.3.
--
--   Differences from the source:
--   - encoding: finite random variables U, Y, Z → functions on a finite sample space Ω carrying a probability vector P; reason: all quantities depend only on the joint law of (U, Y, Z), itself a law on a finite set
--   - encoding: Ψ : Δ(Ω) → ℝ concave → Ψ a real function of real vectors on the value set, concave on the simplex; reason: only values on laws are used
--   - encoding: conditional laws in the expectations defining I_Ψ → condLaw uses the unconditional law at every probability-zero observation; reason: each such conditional-law value is multiplied by the probability zero of the observation, so every information gain is unchanged
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #705 (October 2026), p. 7, Lemma 2.7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/705.pdf

import Mathlib
import Definitions.Def_GirthBethe_Sharp_FiniteInfo

open Finset

namespace GirthBethe.Sharp

/-- Lemma 2.7: for concave `Ψ` and a Markov chain `U – Y – Z`, `I_Ψ(U; Y) ≥ I_Ψ(U; Z) ≥ 0`. -/
theorem concave_information_data_processing {Ω α β γ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ]
    (P : Ω → ℝ) (hP : P ∈ stdSimplex ℝ Ω) (U : Ω → α) (Y : Ω → β) (Z : Ω → γ)
    (Ψ : (α → ℝ) → ℝ) (hΨ : ConcaveOn ℝ (stdSimplex ℝ α) Ψ)
    (hMarkov : ∀ a b c,
      law P (fun ω => (U ω, Y ω, Z ω)) (a, b, c) * law P Y b =
        law P (fun ω => (U ω, Y ω)) (a, b) * law P (fun ω => (Y ω, Z ω)) (b, c)) :
    infoGain Ψ P U Z ≤ infoGain Ψ P U Y ∧ 0 ≤ infoGain Ψ P U Z := by sorry

end GirthBethe.Sharp
