-- Prove2me | Theorems.Thm_LowTempGlauber_theorem_1
-- name    : LowTempGlauber.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:27:27.371424+00:00
-- url     : https://prove2.me/theorems/61be23fe-270a-4631-9628-c68e30858e91
-- title:
--   Theorem 1 — hard-core Glauber dynamics on random bipartite $d$-regular graphs samples each phase in $n^{3/2+o(1)}$ steps; the full law in $n^{2+o(1)}$ time
-- statement:
--   Let $d\ge3$ be an integer, $\delta>0$ and $K>0$, and let $\lambda>\lambda_c(d)+\delta$, where $\lambda_c(d)=\frac{(d-1)^{d-1}}{(d-2)^d}$ is the tree uniqueness threshold. Let $\mu_G$ be the hard-core law $\mu_G(I)\propto\lambda^{|I|}$ on the independent sets of $G$, and $\mu^\pm_G$ its restrictions to the two phases $\mathcal I^+_G=\{M(I)>0\}$ and $\mathcal I^-_G=\{M(I)\le0\}$, where $M(I)=|I\cap V^+|-|I\cap V^-|$. With $\varepsilon=n^{-K}$, there are step counts $T^\pm(n)=\tilde O(n^{3/2})$ and $T_2(n)=\tilde O(n^2)$ and a single program for the unit-cost real RAM with fair coins such that, with high probability over a uniformly random bipartite $d$-regular graph $G\sim\mathcal G^{\mathrm{bip}}_{n,d}$:
--
--   1. Glauber dynamics for $\mu_G$ started from $V^+$ is within total variation distance $\varepsilon$ of $\mu^+_G$ at time $T^+(n)$, and started from $V^-$ it is within $\varepsilon$ of $\mu^-_G$ at time $T^-(n)$;
--   2. on input $n$, $d$, the adjacency lists of $G$ and $\lambda$, the program halts within $T_2(n)$ steps on every sequence of coin flips, and the law of its output independent set is within total variation distance $\varepsilon$ of $\mu_G$.
--
--   This is the paper's main result for the hard-core model. Throughout the non-uniqueness regime, where Glauber dynamics mixes exponentially slowly from worst-case starts, it samples each phase in $n^{3/2+o(1)}$ steps from the natural one-sided start, and the phase samples combine into an $n^{2+o(1)}$-time sampler for the full law.
--
--   **Formalization Note** The step counts depend on $n$ only (and on $d,\delta,K,\lambda$); the program is a single admissible program (rational constants) of the published `SubsetConvFPRAS` real RAM with its value oracles set to $0$, the same for every $n$ and $G$, and it may depend on $d,\delta,K,\lambda$. Its output is bitmap $0$, a set of vertex numbers ($V^+$ numbered first).
--
--   Differences from the source:
--   - reading: "whp over G ∼ G^bip_{n,d}. Let ε = 1/n^K. Then, for any λ > λ_c(d) + δ" → λ fixed before the whp event, the step counts and the program; reason: p.3: the hard-core result applies "to every fixed λ > λ_c(d), with constants that may depend on the distance from the threshold"; the proofs of Lemma 12 and Theorem 1 fix λ first
--   - reading: "within TV-distance ε from μ⁺_G in t = Õ(n^{3/2}) steps. Similarly for (X⁻_t)" → TV distance ≤ n^{−K} at time T⁺(n) (resp. T⁻(n)), for functions of n alone with T±(n) ≤ n^{3/2+ε′} eventually for every ε′ > 0; reason: the unrestricted chain eventually leaves the phase, so the claim is about a time T(n); Õ means up to an n^{o(1)} factor (p.2, p.3)
--   - reading: "an algorithm that outputs in time Õ(n²) an ε-sample from the full distribution μ_G" → one admissible program of the published unit-cost real RAM with fair coins (value oracles 0), the same for all n and G, on input (n, d, sorted adjacency lists, λ), halting within T₂(n) ≤ n^{2+o(1)} steps on every coin tape, whose output law is within n^{−K} of μ_G in TV; reason: the paper names no machine model; the RAM has no exponential, floor or uniform-real primitive and only rational constants, and one program must serve every n, which rules out lookup tables
--   - encoding: whp over G ∼ G^bip_{n,d}; independent sets; V⁺ → AlmostEvery d; configurations Vertex n → Bool; V⁺ = the inl copy of Fin n; reason: the uniform distribution of p.3 and the paper’s objects
-- source:
--   Galanis–Štefankovič, Low-Temperature Sampling via Equilibrium Disagreements, STOC 2027 submission (manuscript sha256 c41a38ff…7533d), Theorem 1, p.4 (part 1 = Lemma 12, p.13; part 2 proved in §3.3.2, pp.18–19)

import Mathlib
import Definitions.Def_mm_mixing
import Definitions.Def_mm_mcmc
import Definitions.Def_mm_coupling
import Definitions.Def_SubsetConvFPRAS_Machine
import Definitions.Def_LowTempGlauber_HardCore
import Definitions.Def_LowTempGlauber_IsNPowLittleO
import Definitions.Def_LowTempGlauber_SamplerInput

open Classical

namespace LowTempGlauber

open ExpanderBIS.RandomHardCore MarkovMixing

/-- Galanis–Štefankovič, *Low-Temperature Sampling via Equilibrium Disagreements*, STOC 2027
submission (manuscript sha256 c41a38ff…), Theorem 1, p.4 (part 1 is Lemma 12, p.13; part 2 is proved
in §3.3.2, pp.18–19).

Let `d ≥ 3` be an integer and `δ > 0`. For any `K > 0`, whp over `G ∼ G^bip_{n,d}`, with `ε = 1/n^K`,
for any `λ > λ_c(d) + δ`:
1. `(X⁺_t)` (Glauber dynamics from `V⁺`) is within TV-distance `ε` from `μ⁺_G` in `t = Õ(n^{3/2})`
   steps; similarly `(X⁻_t)` from `V⁻` and `μ⁻_G`;
2. there is an algorithm that outputs in time `Õ(n²)` an `ε`-sample from the full distribution `μ_G`.

**Formalization Note.**
* `λ` is fixed before the whp event, the step counts and the algorithm (p.3: the hard-core result
  applies "to every fixed `λ > λ_c(d)`"; the proof fixes `λ` first).
* "Within `ε` in `Õ(n^{3/2})` steps": the TV distance at the time `T±(n)`, where `T±` are functions of
  `n` alone with `T±(n) ≤ n^{3/2+o(1)}` (`IsNPowLittleO`).
* The algorithm is one admissible program of the published `SubsetConvFPRAS` unit-cost real RAM with
  fair coins (value oracles `0`), the same for every `n` and `G`. Its input is `n`, `d`, the sorted
  adjacency lists and `λ` (`initSampler`). It halts within `T₂(n) ≤ n^{2+o(1)}` steps on every coin tape,
  and the law of its output (bitmap `0`, a set of vertex numbers) is within `n^{−K}` of `μ_G` in TV.
* `μ_G` is the published `hardcoreDist G λ`; whp is the published `AlmostEvery d`. -/
theorem theorem_1 (d : ℕ) (hd : 3 ≤ d) (δ : ℝ) (hδ : 0 < δ) (K : ℝ) (hK : 0 < K)
    (lam : ℝ) (hlam : lamC d + δ < lam) :
    ∃ Tp Tm T2 : ℕ → ℕ, IsNPowLittleO Tp (3 / 2) ∧ IsNPowLittleO Tm (3 / 2) ∧
      IsNPowLittleO T2 2 ∧
      ∃ P : SubsetConvFPRAS.Program, SubsetConvFPRAS.Admissible P ∧
        AlmostEvery d (fun n G =>
          tvDist (rowDist (glauber (hardcoreDist G lam)) (Tp n) (plusInit n))
              (condLaw (hardcoreDist G lam) (IPlus G)) ≤ (n : ℝ) ^ (-K) ∧
            tvDist (rowDist (glauber (hardcoreDist G lam)) (Tm n) (minusInit n))
              (condLaw (hardcoreDist G lam) (IMinus G)) ≤ (n : ℝ) ^ (-K) ∧
            (∀ bits : Fin (T2 n) → Bool,
              (SubsetConvFPRAS.run P (fun _ => 0) (fun _ => 0) (initSampler n d G lam)
                (SubsetConvFPRAS.extendBits bits) (T2 n)).output.isSome) ∧
            tvDist (outLaw P n d G lam (T2 n))
              (fun S => hardcoreDist G lam (cfgOfSet S)) ≤ (n : ℝ) ^ (-K)) := by sorry

end LowTempGlauber
