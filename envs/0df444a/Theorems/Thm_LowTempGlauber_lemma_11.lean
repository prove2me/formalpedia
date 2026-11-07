-- Prove2me | Theorems.Thm_LowTempGlauber_lemma_11
-- name    : LowTempGlauber.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:27:12.368647+00:00
-- url     : https://prove2.me/theorems/9eba3c2b-d375-44a3-96c4-e4208ee0b294
-- title:
--   Lemma 11 — from $V^+$ at large field $s_0$, the restricted chain is $\varepsilon$-close to $\mu^+_{G,s_0}$ after $4n\log(4n/\varepsilon)$ steps
-- statement:
--   Let $d\ge3$ and $\lambda>0$, and let $s_0>0$ satisfy $\lambda e^{-s_0}\le\frac1{4d^2}$ and $\lambda e^{s_0}\ge10(\lambda+1)^2$. Let $G=(V^+\sqcup V^-,E)$ be a $d$-regular bipartite graph with activities $\lambda e^{s_0}$ on $V^+$ and $\lambda e^{-s_0}$ on $V^-$. Then for every $\varepsilon\ge e^{-n/2}$, Glauber dynamics started from $X_0=V^+$, with proposals outside $\mathcal I^+_G$ rejected, is within total variation distance $\varepsilon$ of $\mu^+_{G,s_0}$ at every time
--   $$t\ge\bigl\lfloor4n\log(4n/\varepsilon)\bigr\rfloor.$$
--
--   This is the starting point of the annealing schedule in Lemma 12 and of the estimators of Theorem 1, part 2.
--
--   **Formalization Note** The chain is heat-bath Glauber dynamics for $\mu^+_{G,s_0}$. The paper says the chain "outputs in $\le4n\log(4n/\varepsilon)$ steps an $\varepsilon$-sample". Since the distance to a stationary law never increases, this is the same as the bound at every $t\ge\lfloor4n\log(4n/\varepsilon)\rfloor$. Here $\log$ is the natural logarithm.
--
--   Differences from the source:
--   - encoding: "outputs in ≤ 4n log(4n/ε) steps an ε-sample" → TV distance ≤ ε at every integer t ≥ ⌊4n log(4n/ε)⌋; reason: equivalent: the TV distance to the stationary law μ⁺_{G,s₀} is non-increasing in t
--   - encoding: Glauber dynamics with proposals outside I⁺_G rejected → glauber μ⁺_{G,s₀} (heat-bath dynamics of μ⁺_{G,s₀}); reason: the same transition matrix on I⁺_G
-- source:
--   Galanis–Štefankovič, Low-Temperature Sampling via Equilibrium Disagreements, STOC 2027 submission (manuscript sha256 c41a38ff…7533d), Lemma 11, p.13 (proof in Appendix B.1, pp.60–61)

import Mathlib
import Definitions.Def_mm_mixing
import Definitions.Def_mm_mcmc
import Definitions.Def_LowTempGlauber_HardCore

open Classical

namespace LowTempGlauber

open ExpanderBIS.RandomHardCore MarkovMixing

/-- Galanis–Štefankovič, *Low-Temperature Sampling via Equilibrium Disagreements*, STOC 2027
submission (manuscript sha256 c41a38ff…), Lemma 11, p.13 (proof in Appendix B.1, pp.60–61).

Let `d ≥ 3`, `λ > 0`, and `s₀ > 0` with `λe^{−s₀} ≤ 1/(4d²)` and `λe^{s₀} ≥ 10(λ + 1)²`. Let `G` be a
`d`-regular bipartite graph with activities `λe^{s₀}` on `V⁺` and `λe^{−s₀}` on `V⁻`. For any
`ε ≥ e^{−n/2}`, Glauber dynamics started from `X₀ = V⁺` with proposals outside `I⁺_G` rejected
outputs in at most `4n log(4n/ε)` steps an `ε`-sample from `μ⁺_{G,s₀}`.

**Formalization Note.** The chain is `glauber μ⁺_{G,s₀}`. "Outputs in at most `T` steps an `ε`-sample"
is stated as: at every time `t ≥ ⌊T⌋` the law is within `ε` of `μ⁺_{G,s₀}` in total variation. Since
the distance to a stationary law is non-increasing in `t`, this is equivalent to the distance being at
most `ε` at some time `t ≤ T`. `log` is the natural logarithm (the proof uses `e^{−t/(4n)}`). -/
theorem lemma_11 (d : ℕ) (hd : 3 ≤ d) (lam : ℝ) (hlam : 0 < lam) (s₀ : ℝ) (hs₀ : 0 < s₀)
    (h₁ : lam * Real.exp (-s₀) ≤ 1 / (4 * (d : ℝ) ^ 2))
    (h₂ : 10 * (lam + 1) ^ 2 ≤ lam * Real.exp s₀)
    (n : ℕ) (G : SimpleGraph (Vertex n)) (hG : IsBipReg G d)
    (ε : ℝ) (hε : Real.exp (-((n : ℝ) / 2)) ≤ ε)
    (t : ℕ) (ht : ⌊4 * (n : ℝ) * Real.log (4 * n / ε)⌋₊ ≤ t) :
    tvDist (rowDist (glauber (muPlus G lam s₀)) t (plusInit n)) (muPlus G lam s₀) ≤ ε := by sorry

end LowTempGlauber
