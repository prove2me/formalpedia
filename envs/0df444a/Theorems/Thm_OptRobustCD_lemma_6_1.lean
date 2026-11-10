-- Prove2me | Theorems.Thm_OptRobustCD_lemma_6_1
-- name    : OptRobustCD.lemma_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:52:22.240868+00:00
-- url     : https://prove2.me/theorems/a958a2ce-fff9-42f4-bba3-154d14f21eb4
-- title:
--   Lemma 6.1 — negative eigenvalue bound for the Bethe Hessian: $n_-(H)\le2$ if $\lambda>0$, $\le1$ if $\lambda<0$, w.h.p.
-- statement:
--   Let $d>0$, $\lambda\in(-1,1)$ with $d\lambda^2>1$, $(G,\sigma^\star)\sim\mathrm{SBM}(n,d,\lambda)$, and $H=H(t)$ the Bethe Hessian at $t=t(d,\lambda)$ of Definition 5.5. With high probability,
--   $$n_-(H)\le\begin{cases}2,&\lambda>0,\\1,&\lambda<0,\end{cases}$$
--   where $n_-(H)$ counts the strictly negative eigenvalues of $H$.
--
--   With Lemma 6.2 it shows that the corrected matrix $M_s$ has exactly one negative eigenvalue (Lemma 5.6).
--
--   Differences from the source:
--   - encoding: with high probability → the SBM(n,d,λ) probability of the event tends to 1 (Whp); reason: the meaning of the phrase
--   - encoding: number of negative eigenvalues → negative real roots of the characteristic polynomial with multiplicity; reason: equal for real symmetric matrices, which M_s and H are
-- source:
--   Hopkins, Hua, Mohanty, Rajaraman, Steurer, Optimal Robust Community Detection, STOC 2027 submission (manuscript of November 3, 2026, sha256 3d287d5422db7c4a43e74333bda1dbed204af51a25fd9f2c6e875ae03a4dafa1), Lemma 6.1, p.28 (pdf p.30)

import Mathlib
import Definitions.Def_OptRobustCD_Whp
import Definitions.Def_OptRobustCD_BetheHessian
import Definitions.Def_OptRobustCD_RowNorms

namespace OptRobustCD

/-- **Lemma 6.1** (Negative eigenvalue bound for the Bethe Hessian). Hopkins, Hua, Mohanty,
Rajaraman, Steurer, *Optimal Robust Community Detection*, STOC 2027 submission (manuscript of
November 3, 2026, sha256 3d287d54…), Lemma 6.1, p.28 (pdf p.30).

"With high probability, `n_−(H) ⩽ 2` if λ > 0, and `n_−(H) ⩽ 1` if λ < 0, where `n_−(H)` counts the
number of strictly negative eigenvalues of H."

**Formalization Note.** Standing assumptions of §6 (p.28): `dλ² > 1`, `H = H(t)` with
`t = t(d, λ)` of Definition 5.5; of §3.1: `d > 0`, `λ ∈ (−1, 1)`, `(G, σ⋆) ∼ SBM(n, d, λ)`.
`λ = 0` is excluded by `dλ² > 1`, so the two cases are `0 < λ` and `λ < 0`. Eigenvalues are
counted with multiplicity. -/
theorem lemma_6_1 (d lam : ℝ) (hd : 0 < d) (hlam : lam ∈ Set.Ioo (-1 : ℝ) 1)
    (hKS : 1 < d * lam ^ 2) :
    Whp d lam (fun _n _σ G =>
      negCount (betheH G (tPar d lam)) ≤ if 0 < lam then 2 else 1) := by sorry

end OptRobustCD
