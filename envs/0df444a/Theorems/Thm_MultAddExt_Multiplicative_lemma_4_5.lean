-- Prove2me | Theorems.Thm_MultAddExt_Multiplicative_lemma_4_5
-- name    : MultAddExt.Multiplicative.lemma_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:47:26.232772+00:00
-- url     : https://prove2.me/theorems/057d7f9a-dd70-4a27-ac2e-f315917c62e5
-- title:
--   Lemma 4.5 — density bounds from statistical distance to uniform
-- statement:
--   Let $P$ be a distribution on a finite set $\Omega$ of size $M$ with $\mathrm{SD}(P,U_\Omega)\le\varepsilon$, and write $p(w)=\Pr[P=w]$. For every $\lambda>0$,
--   $$\Pr_{w\leftarrow U_\Omega}\Bigl[p(w)<\frac{1-\lambda}{M}\Bigr]\le\frac{\varepsilon}{\lambda},\qquad \Pr_{w\leftarrow U_\Omega}\Bigl[p(w)>\frac{1+\lambda}{M}\Bigr]\le\frac{\varepsilon}{\lambda}.$$
--
--   It converts closeness to uniform into pointwise density bounds on most of the domain.
--
--   Differences from the source:
--   - encoding: a (joint) distribution on a finite set → a real mass function p with IsDist p (nonnegative, summing to 1); H∞ = minEntropy (−log₂ of the maximum mass), laws of functions by pushforward; reason: finite distributions are exactly such mass functions; same instances
-- source:
--   Ball, Chattopadhyay, Gurumukhani, Shaltiel, Zhao, Multiplicative and Additive Extractors for Low Entropy Samplable Sources Under Reduced Assumptions, STOC 2027 submission (manuscript sha256 5ac077d7…), p. 19 (PDF 23), Lemma 4.5

import Mathlib
import Definitions.Def_MultAddExt_Multiplicative_FinDist

set_option autoImplicit false

namespace MultAddExt.Multiplicative

/-- **Lemma 4.5** (Density bounds from statistical distance), p. 19. Let `P` be a distribution on a
finite set `Ω` of size `M` with `SD(P, U_Ω) ≤ ε`, and `p(w) = Pr[P = w]`. For every `λ > 0`,
`Pr_{w ← U_Ω}[p(w) < (1 − λ)/M] ≤ ε/λ` and `Pr_{w ← U_Ω}[p(w) > (1 + λ)/M] ≤ ε/λ`. -/
theorem lemma_4_5 {Ω : Type*} [Fintype Ω] (P : Ω → ℝ) (hP : IsDist P) (ε : ℝ)
    (hε : statDist P (uniform Ω) ≤ ε) (lam : ℝ) (hlam : 0 < lam) :
    probEvent (uniform Ω) {w | P w < (1 - lam) / (Fintype.card Ω : ℝ)} ≤ ε / lam ∧
      probEvent (uniform Ω) {w | (1 + lam) / (Fintype.card Ω : ℝ) < P w} ≤ ε / lam := by sorry

end MultAddExt.Multiplicative
