-- Prove2me | Theorems.Thm_LowTempGlauber_theorem_6
-- name    : LowTempGlauber.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:28:17.497208+00:00
-- url     : https://prove2.me/theorems/e4fa10c7-4dad-427b-9d71-47408df4e0fa
-- title:
--   Theorem 6 — whp, $b_{G,\ell,r}(s)\le n^T(e^{-\rho\ell}+(L\ell^2/n)^r)$ and $\mu^+_{G,s}(\mathcal I^{\mathrm{bal}}_G(\theta))\le e^{-\rho n}$ uniformly in $s\in[0,s_0]$
-- statement:
--   Let $d\ge3$ and $\lambda>\lambda_c(d)$, and let $s_0>0$. There are constants $\theta,\rho,L,T>0$ such that, with high probability over a uniformly random bipartite $d$-regular graph $G$ on $V^+\sqcup V^-$ with $|V^\pm|=n$, for all integers $\ell,r\ge1$ and uniformly over all real $s\in[0,s_0]$, with $\mu^+=\mu^+_{G,s}$:
--
--   1. **small disagreement components:** $\displaystyle b_{G,\ell,r}(s)\le n^T\Bigl(e^{-\rho\ell}+\Bigl(\frac{L\ell^2}{n}\Bigr)^r\Bigr)$;
--   2. **balanced independent sets are very unlikely:** $\mu^+\bigl(\mathcal I^{\mathrm{bal}}_G(\theta)\bigr)\le e^{-\rho n}$.
--
--   This is the structural input of the paper: two independent samples from the same phase differ on a linear number of vertices, but their disagreements break into small, tree-like components.
--
--   **Formalization Note** "With high probability" means that the fraction of labelled simple bipartite $d$-regular graphs with sides $V^\pm$ satisfying the property tends to $1$ as $n\to\infty$.
--
--   Differences from the source:
--   - reading: "whp over G ∼ G_n" → whp over the uniform labelled simple bipartite d-regular graph with sides V^± (AlmostEvery d); reason: G_n is not defined in Section 3; the hard-core results are stated for G^bip_{n,d} (p.3), and Lemma 12 applies Theorem 6 to G ∼ G^bip_{n,d}
--   - reading: s₀ (Section 3’s initial field, not bound in the statement) → ∀ s₀ > 0, quantified before the constants θ, ρ, L, T; reason: Section 3 starts "at some large s = s₀" and Lemma 12 applies Theorem 6 "on [0, 2s₀]", so the constants may depend on s₀
--   - reading: "for any ℓ, r ≥ 1" → ℓ, r natural numbers ≥ 1; reason: ℓ and r are the size and tree-excess thresholds of B_{ℓ,r} in (3), which Lemma 7 takes as "integers ℓ, r ≥ 1", and Lemma 12 applies Theorem 6 with integer ℓ = ⌈…⌉ and r = ⌈…⌉
-- source:
--   Galanis–Štefankovič, Low-Temperature Sampling via Equilibrium Disagreements, STOC 2027 submission (manuscript sha256 c41a38ff…7533d), Theorem 6, p.9 (restated and proved pp.34–36)

import Mathlib
import Definitions.Def_LowTempGlauber_Disagreement

open Classical

namespace LowTempGlauber

open ExpanderBIS.RandomHardCore

/-- Galanis–Štefankovič, *Low-Temperature Sampling via Equilibrium Disagreements*, STOC 2027
submission (manuscript sha256 c41a38ff…), Theorem 6, p.9 (restated and proved on pp.34–36).

Let `d ≥ 3` and `λ > λ_c(d)`, and let `s₀ > 0` be the initial field of Section 3. There are constants
`θ, ρ, L, T > 0` such that, whp over the random bipartite `d`-regular graph `G`, for any integers
`ℓ, r ≥ 1`, uniformly over all real `s ∈ [0, s₀]`, with `μ⁺ = μ⁺_{G,s}`:
* small disagreement components: `b_{G,ℓ,r}(s) ≤ n^T (e^{−ρℓ} + (Lℓ²/n)^r)`;
* balanced independent sets are very unlikely: `μ⁺(I^bal_G(θ)) ≤ e^{−ρn}`.

**Formalization Note.** "whp over `G`" is the published `AlmostEvery d`: the fraction of the labelled
simple bipartite `d`-regular graphs on `V⁺ ⊔ V⁻` (`|V±| = n`) satisfying the property tends to `1`.
The page writes `G ∼ G_n`; the graph model of the hard-core results is `G^bip_{n,d}` (p.3). `s₀ > 0` is
universally quantified before the constants, which may depend on it (Lemma 12 applies the theorem on
`[0, 2s₀]`). -/
theorem theorem_6 (d : ℕ) (hd : 3 ≤ d) (lam : ℝ) (hlam : lamC d < lam) (s₀ : ℝ) (hs₀ : 0 < s₀) :
    ∃ θ ρ L T : ℝ, 0 < θ ∧ 0 < ρ ∧ 0 < L ∧ 0 < T ∧
      AlmostEvery d (fun n G =>
        ∀ ℓ r : ℕ, 1 ≤ ℓ → 1 ≤ r → ∀ s ∈ Set.Icc (0 : ℝ) s₀,
          bBad G lam ℓ r s ≤
              (n : ℝ) ^ T * (Real.exp (-(ρ * ℓ)) + (L * (ℓ : ℝ) ^ 2 / n) ^ r) ∧
            ∑ σ ∈ Finset.univ.filter (Ibal G θ), muPlus G lam s σ ≤ Real.exp (-(ρ * n))) := by sorry

end LowTempGlauber
