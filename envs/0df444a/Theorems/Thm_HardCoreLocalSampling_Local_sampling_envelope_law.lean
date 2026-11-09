-- Prove2me | Theorems.Thm_HardCoreLocalSampling_Local_sampling_envelope_law
-- name    : HardCoreLocalSampling.Local.sampling_envelope_law
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:56:04.365243+00:00
-- url     : https://prove2.me/theorems/2e2b8711-1512-4ef6-ac9d-ee958ecdbeee
-- title:
--   Lemma 15 — Sampling the envelope law
-- statement:
--   The multi-index law of Lemma 10 can be sampled exactly using fair bits, with a uniform finite expected number of nonrecursive operations, and every fixed polynomial moment of the sampled degree is finite.
--
--   Precisely, take rational $q_0\ge0$, scale $M/\eta\ge0$, $t\in(0,1)$, and bounds $b$ and $B$. There is a program which on input $d\le b$ and nonnegative rational linear masses of numerator and denominator at most $B$, with total mass $q_0+\sum_iq_{e_i}+(M/\eta)[(1-t)^{-d}-1-dt]\le1$, halts almost surely, outputs each $\alpha$ with probability exactly its envelope mass, otherwise reports the leftover outcome, and has expected work and each moment of the output degree bounded uniformly over inputs.
--
--   Differences from the source:
--   - encoding: an algorithm in the informally described word and bit cost model → a finite program of the Machine language; reason: a concrete instruction set of that model; every such program is an algorithm in the source's model, and restricting address arithmetic to increment, decrement and paid conversion only charges more than the source does
--   - generalization: the multi-index law of Lemma 10, with its specific constants → any rational constants, and any linear masses of bounded size, of total mass at most one; reason: Lemma 10's law is an instance, since its linear masses range over a finite set of rationals; the proof uses nothing else
-- source:
--   Thomas Chen, STOC 2027 submission #462 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/462.pdf, Lemma 15, printed p.13 (PDF p.14)

import Mathlib
import Definitions.Def_HardCoreLocalSampling_Local_Specs

namespace HardCoreLocalSampling.Local

/-- Thomas Chen, STOC 2027 submission #462, Lemma 15, printed p.13 (PDF p.14).
For fixed envelope constants and rational linear masses of bounded size, a fair-bit program takes
`d` and the linear masses as input, halts almost surely, and outputs `α` with probability exactly
`envelopeMass α` (leftover: output `false`, probability `1 - Q`). The expected number of
operations and every fixed polynomial moment of the sampled degree are finite and bounded uniformly
over the inputs. -/
theorem sampling_envelope_law (b B : ℕ) (qConst scale t : ℚ) (hq : 0 ≤ qConst)
    (hscale : 0 ≤ scale) (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ (P : Program) (C : NNReal) (moment : ℕ → NNReal),
      ∀ (d : ℕ), d ≤ b → ∀ lin : Fin d → ℚ, (∀ i, 0 ≤ lin i) →
        (∀ i, (lin i).num.toNat ≤ B ∧ (lin i).den ≤ B) →
        qConst + ∑ i, lin i + tailMass scale t d ≤ 1 →
        let init : Config := { N := regsOf [d], Nm := regsOf (linCells lin) }
        (∀ᵐ ω ∂fairMeasure, outcome P noOracle ω noExt init ≠ none) ∧
        (∀ α : Fin d → ℕ,
          fairMeasure {ω | ∃ c, finalConfig P noOracle ω noExt init = some c ∧
              c.result = some true ∧ readIndex c d = α} =
            ENNReal.ofReal ((envelopeMass qConst lin scale t α : ℚ) : ℝ)) ∧
        ∫⁻ ω, wordWork P noOracle ω noExt init ∂fairMeasure ≤ C ∧
        ∀ p : ℕ, ∫⁻ ω,
          (match finalConfig P noOracle ω noExt init with
            | some c => if c.result = some true then ((mdeg (readIndex c d) : ENNReal) ^ p) else 0
            | none => 0) ∂fairMeasure ≤ moment p := by sorry

end HardCoreLocalSampling.Local
