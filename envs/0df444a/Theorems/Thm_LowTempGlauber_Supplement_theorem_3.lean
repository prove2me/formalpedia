-- Prove2me | Theorems.Thm_LowTempGlauber_Supplement_theorem_3
-- name    : LowTempGlauber.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:29:22.527203+00:00
-- url     : https://prove2.me/theorems/ef33a828-6dbb-4caf-80fb-8f2b20a6bd90
-- title:
--   Theorem 3 — ferromagnetic Ising Glauber dynamics on random $d$-regular graphs samples each phase for $\beta>\beta_c(d)$ in $n^{3/2+o(1)}$ steps; the full law in $n^{3/2+o(1)}$ time
-- statement:
--   Fix an integer $d\ge3$, $\delta>0$ and $K>0$, and let $\beta>\beta_c(d)+\delta$, where $\beta_c(d)=\ln\frac d{d-2}$. Let $\nu_G(\sigma)\propto e^{\beta m(\sigma)}$ be the ferromagnetic Ising law on $\sigma\in\{0,1\}^V$, $m(\sigma)$ the number of monochromatic edges, and $\nu^\pm_G=\nu_G(\cdot\mid\Sigma^\pm)$ its phases, $\Sigma^+=\{|\sigma^{-1}(1)|\ge n/2\}$ and $\Sigma^-=\{|\sigma^{-1}(1)|<n/2\}$. Let $\varepsilon=n^{-K}$.
--
--   There are step counts $T^\pm(n)\le n^{3/2+o(1)}$, a bound $T_2(n)\le n^{3/2+o(1)}$ and one program for the unit-cost real RAM with fair coins such that, with probability $1-o(1)$ over a uniformly random $d$-regular graph $G$ on $n$ vertices:
--   1. Glauber dynamics for $\nu_G$ started from all-plus is within total variation $\varepsilon$ of $\nu^+_G$ at time $T^+(n)$, and started from all-minus it is within $\varepsilon$ of $\nu^-_G$ at time $T^-(n)$;
--   2. on input $n$, $d$, the adjacency lists of $G$ and $\beta$, the program halts within $T_2(n)$ steps on every sequence of coins, and the law of its output configuration is within total variation $\varepsilon$ of $\nu_G$.
--
--   This is the paper's result for the ferromagnetic Ising model throughout the low-temperature regime of random regular graphs. The full sampler is faster than for the other two models because of the spin-flip symmetry.
--
--   **Formalization Note** The step counts and the program depend on $d,\delta,K,\beta$ only. Glauber dynamics is the published single-site heat-bath chain of $\nu_G$ on $\{0,1\}^V$, not restricted to a phase. "With probability $1-o(1)$" is the published `WithHighProb d`; the output is bitmap $0$, the set of spin-$1$ vertices.
--
--   Differences from the source:
--   - reading: "whp over G ∼ G_{n,d}. Let ε = 1/n^K. Then, for any β > β_c(d) + δ" → β fixed before the whp event, the step counts and the program; reason: p.3: the Ising result applies "to every fixed β > β_c(d), with constants that may depend on the distance from the threshold"; the published goal (Theorem 1) is read the same way
--   - reading: "within TV-distance ε from ν⁺_G in t = Õ(n^{3/2}) steps. Similarly for (X⁻_t)" → TV distance ≤ n^{−K} at time T±(n), for functions of n with T±(n) ≤ n^{3/2+ε′} eventually for every ε′ > 0; reason: the unrestricted chain eventually leaves its phase, so the claim is about a time T(n); Õ means up to an n^{o(1)} factor (p.5)
--   - reading: "an algorithm that outputs in time Õ(n^{3/2}) an ε-sample from the full distribution ν_G" → one admissible program of the published unit-cost real RAM with fair coins (value oracles 0), the same for all n and G, on input (n, d, sorted adjacency lists, β), halting within T₂(n) ≤ n^{3/2+o(1)} steps on every coin tape, whose output law (the spin-1 vertices) is within n^{−K} of ν_G; reason: the paper names no machine model; one program for every n rules out lookup tables
--   - encoding: σ ∈ {0,1}^V; Σ⁺ = {|σ^{−1}(1)| ≥ n/2}; whp over G ∼ G_{n,d} → σ : Fin n → Bool with true = 1; n ≤ 2|σ^{−1}(1)|; WithHighProb d; reason: Lean convention; the same configurations and the published uniform d-regular ensemble
-- source:
--   Galanis–Štefankovič, Low-Temperature Sampling via Equilibrium Disagreements, STOC 2027 submission (manuscript sha256 c41a38ff…7533d), Theorem 3, p.5 (proved in §4 and §8)

import Mathlib
import Definitions.Def_mm_mixing
import Definitions.Def_mm_mcmc
import Definitions.Def_SubsetConvFPRAS_Machine
import Definitions.Def_PottsRapidMixing_Ensemble
import Definitions.Def_LowTempGlauber_IsNPowLittleO
import Definitions.Def_LowTempGlauber_Supplement_FinSampler
import Definitions.Def_LowTempGlauber_Supplement_Ising

open Classical

namespace LowTempGlauber.Supplement

open MarkovMixing PottsRapidMixing

/-- Galanis–Štefankovič, *Low-Temperature Sampling via Equilibrium Disagreements*, STOC 2027
submission (manuscript sha256 c41a38ff…7533d), Theorem 3, p.5 (proved in §4 and §8).

Fix an integer `d ≥ 3` and `δ > 0`. For any `K > 0`, whp over `G ∼ G_{n,d}`, with `ε = n^{−K}`, for any
`β > β_c(d) + δ` (`β_c(d) = ln(d/(d−2))`):
1. Ising Glauber dynamics from all-plus is within TV-distance `ε` of `ν⁺_G` in `Õ(n^{3/2})` steps;
   similarly from all-minus and `ν⁻_G`;
2. there is an algorithm that outputs in time `Õ(n^{3/2})` an `ε`-sample from `ν_G`.

**Formalization Note.**
* `β` is fixed before the whp event, the step counts and the algorithm (p.3: the Ising result applies
  "to every fixed `β > β_c(d)`, with constants that may depend on the distance from the threshold").
* The chains are the unrestricted single-site heat-bath Glauber dynamics `glauber (isingLaw G β)` on
  `Fin n → Bool`; the targets are `ν_G(· | Σ^±)`.
* The algorithm is one admissible program of the published unit-cost real RAM with fair coins (value
  oracles `0`), the same for every `n` and `G`, on input `n, d`, the sorted adjacency lists and `β`
  (real cell 0); it halts within `T₂(n) ≤ n^{3/2+o(1)}` steps on every coin tape and the law of its
  output (bitmap `0`, the spin-1 vertices) is within `n^{−K}` of `ν_G` in TV. Whp is the published
  `WithHighProb d`. -/
theorem theorem_3 (d : ℕ) (hd : 3 ≤ d) (δ : ℝ) (hδ : 0 < δ) (K : ℝ) (hK : 0 < K)
    (β : ℝ) (hβ : betaCIsing d + δ < β) :
    ∃ Tp Tm T₂ : ℕ → ℕ, LowTempGlauber.IsNPowLittleO Tp (3 / 2) ∧
      LowTempGlauber.IsNPowLittleO Tm (3 / 2) ∧ LowTempGlauber.IsNPowLittleO T₂ (3 / 2) ∧
      ∃ P : SubsetConvFPRAS.Program, SubsetConvFPRAS.Admissible P ∧
        WithHighProb d (fun n G =>
          tvDist (rowDist (glauber (isingLaw G β)) (Tp n) (allPlus n))
              (condLaw (isingLaw G β) IsSigmaPlus) ≤ (n : ℝ) ^ (-K) ∧
            tvDist (rowDist (glauber (isingLaw G β)) (Tm n) (allMinus n))
              (condLaw (isingLaw G β) IsSigmaMinus) ≤ (n : ℝ) ^ (-K) ∧
            (∀ bits : Fin (T₂ n) → Bool,
              (SubsetConvFPRAS.run P (fun _ => 0) (fun _ => 0) (isingInit n d G β)
                (SubsetConvFPRAS.extendBits bits) (T₂ n)).output.isSome) ∧
            tvDist (outLaw P (isingInit n d G β) (T₂ n)) (pushLaw (isingLaw G β) spinSet)
              ≤ (n : ℝ) ^ (-K)) := by sorry

end LowTempGlauber.Supplement
