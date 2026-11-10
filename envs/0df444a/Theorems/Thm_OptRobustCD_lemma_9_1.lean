-- Prove2me | Theorems.Thm_OptRobustCD_lemma_9_1
-- name    : OptRobustCD.lemma_9_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:51:46.73969+00:00
-- url     : https://prove2.me/theorems/6512e49c-44ab-42d9-a8ea-2aa9bc3b4bef
-- title:
--   Lemma 9.1 — lifting the vertex walk score: $\|\frac{(d\lambda)^2}{(d\lambda)^2-1}R_G\sigma^{(s)}-W^{(s)}\|\le\varepsilon\sqrt n$
-- statement:
--   Let $d>0$, $\lambda\in(-1,1)$ with $d\lambda^2>1$, and $(G,\sigma^\star)\sim\mathrm{SBM}(n,d,\lambda)$. For every $\varepsilon>0$ there is $s_0=s_0(d,\lambda,\varepsilon)$ such that for every fixed $s\ge s_0$, with high probability,
--   $$\Bigl\|\frac{(d\lambda)^2}{(d\lambda)^2-1}\cdot R_G\frac{A^{(s)}_G\sigma^\star}{(d\lambda)^s}-W^{(s)}\Bigr\|\le\varepsilon\sqrt n,$$
--   where $(R_Gx)_{u\to v}=x_v-x_u/(d\lambda)$ and $W^{(s)}$ is the walk score.
--
--   It reduces estimating the informative eigenvector on directed edges to estimating the vertex vector $\sigma^{(s)}$ (Lemma 5.3).
--
--   Differences from the source:
--   - encoding: with high probability → the SBM(n,d,λ) probability of the event tends to 1 (Whp); reason: the meaning of the phrase
-- source:
--   Hopkins, Hua, Mohanty, Rajaraman, Steurer, Optimal Robust Community Detection, STOC 2027 submission (manuscript of November 3, 2026, sha256 3d287d5422db7c4a43e74333bda1dbed204af51a25fd9f2c6e875ae03a4dafa1), Lemma 9.1, p.44 (pdf p.46)

import Mathlib
import Definitions.Def_OptRobustCD_Whp
import Definitions.Def_OptRobustCD_nbWalks
import Definitions.Def_OptRobustCD_Lift

namespace OptRobustCD

/-- **Lemma 9.1** (Lifting the vertex walk score). Hopkins, Hua, Mohanty, Rajaraman, Steurer,
*Optimal Robust Community Detection*, STOC 2027 submission (manuscript of November 3, 2026, sha256
3d287d54…), Lemma 9.1, p.44 (pdf p.46).

"Let (G, σ⋆) ∼ SBM(n, d, λ) with dλ² > 1, and let `W^{(ℓ)}` be the walk scores of Section 4. For
every ε > 0 there is `s_0 = s_0(d, λ, ε)` such that for every fixed `s ⩾ s_0`, with high probability,
`∥((dλ)²/((dλ)² − 1)) · R_G(A^{(s)}_G σ⋆/(dλ)^s) − W^{(s)}∥ ⩽ ε√n`."

**Formalization Note.** `A^{(s)}_G σ⋆/(dλ)^s` is `σ^{(s)}` (`sigmaS`); `R_G` is `liftR`; the norm is
Euclidean on ordered pairs. `d > 0`, `λ ∈ (−1, 1)` are the standing assumptions of §3.1 (p.12). -/
theorem lemma_9_1 (d lam : ℝ) (hd : 0 < d) (hlam : lam ∈ Set.Ioo (-1 : ℝ) 1)
    (hKS : 1 < d * lam ^ 2) (ε : ℝ) (hε : 0 < ε) :
    ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → Whp d lam (fun n σ G =>
      l2 (fun p => ((d * lam) ^ 2 / ((d * lam) ^ 2 - 1)) * liftR d lam G (sigmaS d lam s G σ) p -
        walkScore d lam s G σ p) ≤ ε * Real.sqrt n) := by sorry

end OptRobustCD
