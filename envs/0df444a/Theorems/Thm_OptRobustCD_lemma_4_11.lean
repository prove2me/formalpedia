-- Prove2me | Theorems.Thm_OptRobustCD_lemma_4_11
-- name    : OptRobustCD.lemma_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:50:58.020943+00:00
-- url     : https://prove2.me/theorems/864bed7c-91cc-4c71-b42d-f968e13c57cc
-- title:
--   Lemma 4.11 — neighborhoods are small on average: $\sum_v|B_G(v,s)|^3\le Cn$ w.h.p.
-- statement:
--   Let $d>0$, $\lambda\in(-1,1)$ with $d\lambda^2>1$, and $(G,\sigma^\star)\sim\mathrm{SBM}(n,d,\lambda)$. For every $s\ge1$ there is $C=C(d,\lambda,s)$ such that, with high probability,
--   $$\sum_{v\in[n]}|B_G(v,s)|^3\le Cn.$$
--
--   Together with Lemma 4.10 this gives the stability of BP in the block model (Lemmas 4.5, 4.6).
--
--   Differences from the source:
--   - encoding: with high probability → the SBM(n,d,λ) probability of the event tends to 1 (Whp); reason: the meaning of the phrase
-- source:
--   Hopkins, Hua, Mohanty, Rajaraman, Steurer, Optimal Robust Community Detection, STOC 2027 submission (manuscript of November 3, 2026, sha256 3d287d5422db7c4a43e74333bda1dbed204af51a25fd9f2c6e875ae03a4dafa1), Lemma 4.11, p.21 (pdf p.23)

import Mathlib
import Definitions.Def_OptRobustCD_Whp
import Definitions.Def_OptRobustCD_DirEdges

namespace OptRobustCD

/-- **Lemma 4.11** (Neighborhoods are small on average). Hopkins, Hua, Mohanty, Rajaraman,
Steurer, *Optimal Robust Community Detection*, STOC 2027 submission (manuscript of November 3,
2026, sha256 3d287d54…), Lemma 4.11, p.21 (pdf p.23).

"Let dλ² > 1 and (G, σ⋆) ∼ SBM(n, d, λ). For every s ⩾ 1 there is C = C(d, λ, s) such that, with
high probability, `Σ_{v∈[n]} |B_G(v, s)|³ ⩽ Cn`."

**Formalization Note.** `d > 0`, `λ ∈ (−1, 1)` are the standing assumptions of §3.1 (p.12).
`C` is chosen after `d, λ, s` and before `n`. -/
theorem lemma_4_11 (d lam : ℝ) (hd : 0 < d) (hlam : lam ∈ Set.Ioo (-1 : ℝ) 1)
    (hKS : 1 < d * lam ^ 2) (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℝ, Whp d lam (fun n _σ G => ∑ v, (ballCard G v s : ℝ) ^ 3 ≤ C * n) := by sorry

end OptRobustCD
