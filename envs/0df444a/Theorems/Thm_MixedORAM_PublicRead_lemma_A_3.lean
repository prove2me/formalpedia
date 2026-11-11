-- Prove2me | Theorems.Thm_MixedORAM_PublicRead_lemma_A_3
-- name    : MixedORAM.PublicRead.lemma_A_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:49:53.478011+00:00
-- url     : https://prove2.me/theorems/e777386f-dbcd-44da-8329-0d37e8c45711
-- title:
--   Lemma A.3 — transfer of an observable event (statistical: loss δ; computational: loss 1/64 + negligible)
-- statement:
--   **Statistical part.** Let $I$ be an implementation with statistical trace privacy on horizon $\bar N$ with distance $\delta$ under a leakage. Let $(A_0,U_{\mathrm{alt}},U_{\mathrm{ref}},Z)$ be drawn from any joint law, independent of the implementation's randomness, such that every outcome has $U_{\mathrm{alt}}$ and $U_{\mathrm{ref}}$ comparable and of length at most $\bar N$, and let $E$ be an event depending only on $Z$ and the observed trace. Then
--   $$\Pr_{\mathrm{ref}}(E)\ \ge\ \Pr_{\mathrm{alt}}(E)-\delta,$$
--   where $\Pr_{\mathrm{alt}}$ and $\Pr_{\mathrm{ref}}$ run $I$ on $(A_0,U_{\mathrm{alt}})$ and $(A_0,U_{\mathrm{ref}})$.
--
--   **Computational part.** Let $A$ be a computationally trace-private family under the leakage and $\pi$ a parameter sequence in a polynomial range. Suppose (T1) the input pair and $Z$ are produced by a valid (nonuniform polynomial-time) sampler, with $U_{\mathrm{alt}}=u_0$ and $U_{\mathrm{ref}}=u_1$; (T2) $E(\kappa,z,\mathrm{tr})$ is decided by one machine in time polynomial in its input $(1^\kappa,z,\mathrm{tr})$; (T3) the exact reference trace, preprocessing included, has expected length at most $(\kappa+2)^c$ for some $c$. Then there is a negligible $\nu$ with
--   $$\Pr_{\mathrm{ref}}(E)\ \ge\ \Pr_{\mathrm{alt}}(E)-\frac1{64}-\nu(\kappa)\qquad\text{for all }\kappa .$$
--
--   This lemma moves an event observed on an altered execution, about which the information step reasons, to the reference execution that the workload costs measure; no expected-cost bound on the altered input is needed.
--
--   Differences from the source:
--   - reading: statistical privacy with distance δ → StatPrivate k I N̄ δ, with every sampled pair comparable and of length at most N̄; reason: privacy is defined on a horizon (§2.2); the pairs the lemma compares must lie in it
--   - encoding: E depends only on Z and the address trace; Pr_ref(E) ≥ Pr_alt(E) − δ → E : ζ → Trace a → Prop on the observed trace; Pr_alt(E) ≤ Pr_ref(E) + δ in [0, ∞]; reason: the observed trace is the paper's address trace (addresses, directions, boundaries); the two forms of the inequality are equivalent
--   - encoding: (T1) the input pair is samplable by a nonuniform polynomial-time sampler and its length and fields are polynomial → a valid Sampler (polynomial-size MCircuit family whose output is the code of (A₀, u_alt, u_ref, z), every pair comparable) for a parameter sequence in a polynomial range; reason: a polynomial-size circuit's output has polynomial length
--   - generalization: (T2) E can be tested in time polynomial in the observed trace length → E decided by one machine (published LaconicBarrier.PolyTimeOn) in time polynomial in the length of (1^κ, code of z, code of the trace); reason: E depends on Z, so its test reads Z; allowing time polynomial in κ and |z| as well admits more tests, a weaker hypothesis
--   - encoding: (T3) the exact reference trace has expected length at most a polynomial P(κ) → the expected number of probes of the reference run, preprocessing included, is at most (κ+2)^c; reason: the standard form of a polynomial bound
--   - encoding: nonuniform polynomial-time samplers and distinguishers; polynomial probe cutoffs; negligible advantage (Appendix G) → samplers are polynomial-size multi-output circuit families (published LaconicBarrier.MCircuit) on uniform coins whose output is a fixed injective code of (A₀, u₀, u₁, z); distinguishers are the published NoisyOWMPC.Distinguisher (polynomial-size circuits); cutoffs b(κ) ≤ (κ+2)^c; advantage negligible in the sense of the published NoisyOWMPC.Negligible; reason: circuit families are the nonuniform polynomial-time model; randomness of a nonuniform distinguisher can be fixed to its best value
-- source:
--   Ciszewski, Ragnoli, Access Cost Tradeoffs in Mixed-Mode Oblivious RAM, STOC 2027 submission (manuscript sha256 a4f849fd…), p. 15, Lemma A.3

import Mathlib
import Definitions.Def_MixedORAM_PublicRead_CompPrivacy
import Definitions.Def_LaconicBarrier_PolyTimeOn

set_option autoImplicit false

namespace MixedORAM.PublicRead

theorem lemma_A_3 :
    (∀ (n w m a : ℕ) (k : LeakKind) (I : Impl n w m a) (Nbar : ℕ) (δ : ENNReal),
      StatPrivate k I Nbar δ →
      ∀ {ζ : Type}
        (σ : PMF ((Fin n → BitVec w) × List (Request n w) × List (Request n w) × ζ)),
        (∀ x ∈ σ.support, Comparable k x.2.1 x.2.2.1 ∧ x.2.1.length ≤ Nbar) →
        ∀ E : ζ → Trace a → Prop,
          pexp σ (fun x => (I.traceDist x.1 x.2.1).toOuterMeasure {tr | E x.2.2.2 tr}) ≤
            pexp σ (fun x => (I.traceDist x.1 x.2.2.1).toOuterMeasure {tr | E x.2.2.2 tr}) + δ) ∧
    (∀ (k : LeakKind) (A : Family), CompPrivate k A →
      ∀ (d : ℕ) (π : ℕ → Params), (∀ κ, (π κ).Within d κ) →
        ∀ S : Sampler π, S.Valid k →
          ∀ E : (κ : ℕ) → List Bool → Trace (π κ).a → Bool,
            LaconicBarrier.PolyTimeOn (ι := (κ : ℕ) × List Bool × Trace (π κ).a)
              (fun i => [LaconicBarrier.unary i.1, encStr i.2.1,
                encTrunc (flatTrace i.2.2, false)])
              (fun i => [E i.1 i.2.1 i.2.2]) →
            (∃ c : ℕ, ∀ κ, samplerExpProbes A S κ true ≤ ((κ + 2 : ℕ) : ENNReal) ^ c) →
            ∃ ν : ℕ → ℝ, NoisyOWMPC.Negligible ν ∧ ∀ κ,
              samplerEventProb A S E κ false - 1 / 64 - ν κ ≤
                samplerEventProb A S E κ true) := by sorry

end MixedORAM.PublicRead
