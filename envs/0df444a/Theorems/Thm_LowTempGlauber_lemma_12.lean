-- Prove2me | Theorems.Thm_LowTempGlauber_lemma_12
-- name    : LowTempGlauber.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:27:19.283321+00:00
-- url     : https://prove2.me/theorems/9bef9453-73cd-4053-8f0c-87879dd66c6e
-- title:
--   Lemma 12 — whp, Glauber dynamics from $V^\pm$ is $n^{-K}$-close to $\mu^\pm_G$ after $n^{3/2+o(1)}$ steps (Theorem 1, part 1)
-- statement:
--   Let $d\ge3$ be an integer, $\delta>0$ and $K>0$, and let $\lambda>\lambda_c(d)+\delta$. There are step counts $T^+(n),T^-(n)=\tilde O(n^{3/2})$ such that, with high probability over a uniformly random bipartite $d$-regular graph $G\sim\mathcal G^{\mathrm{bip}}_{n,d}$:
--
--   1. Glauber dynamics $(X^+_t)$ for the hard-core law $\mu_G$ started from $V^+$ is within total variation distance $\varepsilon=n^{-K}$ of $\mu^+_G=\mu_G(\cdot\mid\mathcal I^+_G)$ at time $T^+(n)$;
--   2. similarly, $(X^-_t)$ started from $V^-$ is within $n^{-K}$ of $\mu^-_G=\mu_G(\cdot\mid\mathcal I^-_G)$ at time $T^-(n)$.
--
--   This is the first part of Theorem 1: throughout the non-uniqueness regime, the standard Glauber dynamics started from a one-sided independent set samples its phase in $n^{3/2+o(1)}$ steps.
--
--   **Formalization Note** The chain is the unrestricted heat-bath Glauber dynamics of $\mu_G$ (choose one of the $2n$ vertices uniformly and resample it).
--
--   Differences from the source:
--   - reading: "whp over G ∼ G^bip_{n,d}. Then, for any λ > λ_c(d) + δ" → λ fixed before the whp event and before the step counts; reason: p.3: the hard-core result applies "to every fixed λ > λ_c(d), with constants that may depend on the distance from the threshold", and the proof fixes λ before choosing the graph event
--   - reading: "within TV-distance ε from μ⁺_G in t = Õ(n^{3/2}) steps" → TV distance ≤ n^{−K} at time T⁺(n), for functions T⁺, T⁻ of n alone with T±(n) ≤ n^{3/2+ε′} eventually for every ε′ > 0; reason: the unrestricted chain eventually leaves the phase, so the claim is about a time T(n); Õ means up to an n^{o(1)} factor (p.2, p.3)
--   - encoding: whp over G ∼ G^bip_{n,d} → AlmostEvery d (the fraction of labelled bipartite d-regular graphs with the property tends to 1); reason: the uniform distribution of p.3
-- source:
--   Galanis–Štefankovič, Low-Temperature Sampling via Equilibrium Disagreements, STOC 2027 submission (manuscript sha256 c41a38ff…7533d), Lemma 12, p.13 (proof pp.13–15)

import Mathlib
import Definitions.Def_mm_mixing
import Definitions.Def_mm_mcmc
import Definitions.Def_mm_coupling
import Definitions.Def_LowTempGlauber_HardCore
import Definitions.Def_LowTempGlauber_IsNPowLittleO

open Classical

namespace LowTempGlauber

open ExpanderBIS.RandomHardCore MarkovMixing

/-- Galanis–Štefankovič, *Low-Temperature Sampling via Equilibrium Disagreements*, STOC 2027
submission (manuscript sha256 c41a38ff…), Lemma 12, p.13 (proof pp.13–15); part 1 of Theorem 1.

Let `d ≥ 3` be an integer and `δ > 0`. For any `K > 0`, whp over `G ∼ G^bip_{n,d}`: for any
`λ > λ_c(d) + δ`, the chain `(X⁺_t)` (Glauber dynamics from `V⁺`) is within TV-distance `ε = 1/n^K`
from `μ⁺_G` in `t = Õ(n^{3/2})` steps. Similarly for `(X⁻_t)` from `V⁻` and `μ⁻_G`.

**Formalization Note.** `λ` is fixed before the whp event and before the step counts (p.3: the
hard-core result applies "to every fixed `λ > λ_c(d)`", and the proof fixes `λ` before choosing the
graph event). The step counts `T⁺(n), T⁻(n)` are functions of `n` alone with
`T±(n) ≤ n^{3/2 + o(1)}` (`IsNPowLittleO`), and the distance is evaluated at time `T±(n)`. The chain is
`glauber` of the hard-core law `hardcoreDist G λ` on `Vertex n → Bool`; `μ⁺_G` and `μ⁻_G` are that law
conditioned on `I⁺_G` and `I⁻_G`. -/
theorem lemma_12 (d : ℕ) (hd : 3 ≤ d) (δ : ℝ) (hδ : 0 < δ) (K : ℝ) (hK : 0 < K)
    (lam : ℝ) (hlam : lamC d + δ < lam) :
    ∃ Tp Tm : ℕ → ℕ, IsNPowLittleO Tp (3 / 2) ∧ IsNPowLittleO Tm (3 / 2) ∧
      AlmostEvery d (fun n G =>
        tvDist (rowDist (glauber (hardcoreDist G lam)) (Tp n) (plusInit n))
            (condLaw (hardcoreDist G lam) (IPlus G)) ≤ (n : ℝ) ^ (-K) ∧
          tvDist (rowDist (glauber (hardcoreDist G lam)) (Tm n) (minusInit n))
            (condLaw (hardcoreDist G lam) (IMinus G)) ≤ (n : ℝ) ^ (-K)) := by sorry

end LowTempGlauber
