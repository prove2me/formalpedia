-- Prove2me | Theorems.Thm_OptRobustCD_lemma_4_3
-- name    : OptRobustCD.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:51:28.070743+00:00
-- url     : https://prove2.me/theorems/3f525dfc-a3c9-40a8-a7dd-4b87ef386e48
-- title:
--   Lemma 4.3 — the informative eigenvector is close to a walk score: $\langle\xi,W^{(\ell)}\rangle^2/\|W^{(\ell)}\|^2\to1-O((d\lambda^2)^{-\ell})$
-- statement:
--   Let $d>0$, $\lambda\in(-1,1)$ with $d\lambda^2>1$, let $(G,\sigma^\star)\sim\mathrm{SBM}(n,d,\lambda)$, and let $\xi$ be a unit eigenvector of the nonbacktracking matrix $B_G$ for its eigenvalue of second-largest modulus. There is $C=C(d,\lambda)$ such that for every fixed $\ell\ge0$ and every $\delta>0$, with high probability such a $\xi$ exists and every such $\xi$ satisfies
--   $$\Bigl|\frac{\langle\xi,W^{(\ell)}\rangle^2}{\|W^{(\ell)}\|^2}-1\Bigr|\le C(d\lambda^2)^{-\ell}+\delta,$$
--   where $W^{(\ell)}$ is the walk score. That is, $\langle\xi,W^{(\ell)}\rangle^2/\|W^{(\ell)}\|^2\to1-O((d\lambda^2)^{-\ell})$ in probability.
--
--   It gives a local description of the informative eigenvector: its entry on $u\to v$ is essentially a function of the labels near the edge.
--
--   Differences from the source:
--   - reading: → 1 − O((dλ²)^{−ℓ}) in probability → ∃ C(d,λ), ∀ ℓ, ∀ δ > 0, w.h.p. |ratio − 1| ⩽ C(dλ²)^{−ℓ} + δ; reason: the meaning of convergence in probability to a value within O((dλ²)^{−ℓ}) of 1; the ratio is at most 1
--   - reading: let ξ be a unit eigenvector for the eigenvalue of B_G of second-largest modulus → inside the event: such a ξ (IsInfEig) exists, and the conclusion holds for every such ξ; reason: the paper presumes the eigenvalue real and simple, which holds w.h.p.; the existence clause rules out vacuity
--   - encoding: with high probability → the SBM(n,d,λ) probability of the event tends to 1 (Whp); reason: the meaning of the phrase
--   - encoding: quotients the source writes only where they are defined → Lean's x/0 = 0 at a zero denominator; reason: changes no instance where the source's quotient is defined; on the high-probability event the denominators are nonzero
-- source:
--   Hopkins, Hua, Mohanty, Rajaraman, Steurer, Optimal Robust Community Detection, STOC 2027 submission (manuscript of November 3, 2026, sha256 3d287d5422db7c4a43e74333bda1dbed204af51a25fd9f2c6e875ae03a4dafa1), Lemma 4.3, p.16 (pdf p.18)

import Mathlib
import Definitions.Def_OptRobustCD_Whp
import Definitions.Def_OptRobustCD_NBMatrix
import Definitions.Def_OptRobustCD_nbWalks

namespace OptRobustCD

/-- **Lemma 4.3** (The eigenvector is close to a walk score). Hopkins, Hua, Mohanty, Rajaraman,
Steurer, *Optimal Robust Community Detection*, STOC 2027 submission (manuscript of November 3,
2026, sha256 3d287d54…), Lemma 4.3, p.16 (pdf p.18).

"Let dλ² > 1, let (G, σ⋆) ∼ SBM(n, d, λ), and let ξ be as in Theorem 4.2. For every fixed ℓ ⩾ 0,
`⟨ξ, W^{(ℓ)}⟩²/∥W^{(ℓ)}∥² → 1 − O((dλ²)^{−ℓ})` in probability."

**Formalization Note.** "→ 1 − O((dλ²)^{−ℓ}) in probability" is read as: there is `C` depending on
`d, λ` only such that for every `ℓ` and every `δ > 0`, with high probability the ratio is within
`C(dλ²)^{−ℓ} + δ` of `1` (it is at most `1` by Cauchy–Schwarz). "ξ as in Theorem 4.2" is a unit
eigenvector of `B_G` for the eigenvalue of second-largest modulus (`IsInfEig`); the event asserts
that one exists and quantifies over all of them. `d > 0`, `λ ∈ (−1, 1)` are the standing
assumptions of §3.1 (p.12). -/
theorem lemma_4_3 (d lam : ℝ) (hd : 0 < d) (hlam : lam ∈ Set.Ioo (-1 : ℝ) 1)
    (hKS : 1 < d * lam ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ ℓ : ℕ, ∀ δ : ℝ, 0 < δ → Whp d lam (fun n σ G =>
      (∃ ξ : EVec n, IsInfEig G ξ) ∧ ∀ ξ : EVec n, IsInfEig G ξ →
        |ip ξ (walkScore d lam ℓ G σ) ^ 2 / l2 (walkScore d lam ℓ G σ) ^ 2 - 1| ≤
          C * (d * lam ^ 2) ^ (-(ℓ : ℤ)) + δ) := by sorry

end OptRobustCD
