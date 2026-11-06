-- Prove2me | Theorems.Thm_KMPMixing_lemma_4_13
-- name    : KMPMixing.lemma_4_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:11:43.746074+00:00
-- url     : https://prove2.me/theorems/e2467700-b348-44b6-9d2d-4b213e0471be
-- title:
--   Lemma 4.13 — distance at most $4/d^2$ after $k_0+T$ steps when $t>d^{1000}$
-- statement:
--   Let $G=(V=[d],E)$ be a connected graph, $\gamma=\gamma^{(1,G)}_{\mathrm{KMP}}=1-\lambda_2(M^{(1,G)}_{\mathrm{KMP}})$, $d\ge3$ and $t>d^{1000}$. Let $k_0=100\gamma^{-1}\log d$, $T=6\gamma^{-1}\log d$ and $k_\star=k_0+T$. Then
--   $$
--   \sup_{r\in\Delta_G}\big\|M^{k_\star}_{\mathrm{KMP}}(r,\cdot)-\pi_{\mathrm{KMP}}\big\|_{\mathrm{TV}}\le\frac4{d^2}.
--   $$
--   Here $\log$ is the natural logarithm.
--
--   For many particles, $O(\gamma^{-1}\log d)$ steps bring the chain within $4/d^2$ of equilibrium, independently of $t$; Fact 2.5 then boosts this to any accuracy.
--
--   Differences from the source:
--   - reading: the real numbers $k_0=100\gamma^{-1}\log d$, $T=6\gamma^{-1}\log d$ as step counts → every pair of naturals $k_0\ge100\gamma^{-1}\log d$, $T\ge6\gamma^{-1}\log d$; reason: a matrix power needs an integer exponent; the proof uses $k_0$, $T$ only as lower bounds, and the statement includes the ceilings
--   - encoding: $\gamma$ (spectral gap, $\lambda_2$ in absolute value) → `MarkovMixing.absSpectralGap` of the $t=1$ KMP chain; reason: the source's $\lambda_2$ is the second largest eigenvalue in absolute value (Fact 2.4)
-- source:
--   Chen et al., arXiv:2609.38044, Lemma 4.13, p.29 (PDF p.31); γ, p.29

import Mathlib
import Definitions.Def_KMPMixing_kmpChain
open MarkovMixing

namespace KMPMixing

/-- **Lemma 4.13** (arXiv:2609.38044, p.29 (PDF p.31)). Let `G = ([d], E)` be a connected graph and
`γ = γ^{(1,G)}_KMP = 1 − λ₂(M^{(1,G)}_KMP)`. Assume `d ≥ 3` and `t > d^{1000}`. Let
`k₀ = 100γ^{−1} log d`, `T = 6γ^{−1} log d` and `k⋆ = k₀ + T`. Then
`sup_{r ∈ Δ_G} ‖M^{k⋆}_KMP(r, ·) − π_KMP‖_TV ≤ 4/d²`.

**Formalization Note** `γ` is `MarkovMixing.absSpectralGap` of the `t = 1` KMP chain (`λ₂` in
absolute value, Fact 2.4); `log` is the natural logarithm. The printed `k₀`, `T` are reals; the
statement is made for every pair of natural numbers `k₀ ≥ 100γ^{−1} log d`, `T ≥ 6γ^{−1} log d`
(the proof uses `k₀`, `T` only as lower bounds), which includes their ceilings. The supremum
over `r` is `MarkovMixing.distStationary`. -/
theorem lemma_4_13 {d : ℕ} (hd : 3 ≤ d) {t : ℕ} (ht : d ^ 1000 < t)
    (G : SimpleGraph (Fin d)) [DecidableRel G.Adj] (hG : G.Connected) (k₀ T : ℕ)
    (hk₀ : 100 * (absSpectralGap (kmpChain G 1))⁻¹ * Real.log d ≤ (k₀ : ℝ))
    (hT : 6 * (absSpectralGap (kmpChain G 1))⁻¹ * Real.log d ≤ (T : ℝ)) :
    distStationary (kmpChain G t) (uniformDist (State d t)) (k₀ + T) ≤ 4 / (d : ℝ) ^ 2 := by sorry

end KMPMixing
