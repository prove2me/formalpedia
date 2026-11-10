-- Prove2me | Theorems.Thm_OptRobustCD_lemma_4_5
-- name    : OptRobustCD.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:52:26.689475+00:00
-- url     : https://prove2.me/theorems/e36d6d21-185f-4531-b649-ddf2e560c561
-- title:
--   Lemma 4.5 — BP is stable under changes to the initialization: $|\mathrm{Ov}_{t,\gamma}(G,y)-\mathrm{Ov}_{t,\gamma}(G,y')|\le C\|y-y'\|$
-- statement:
--   Let $d>0$, $\lambda\in(-1,1)$ with $d\lambda^2>1$, and $(G,\sigma^\star)\sim\mathrm{SBM}(n,d,\lambda)$. For every $t\ge1$ there is $C=C(d,\lambda,t)>0$ such that with high probability, for all $\gamma\in(0,1)$ and all $y,y'\in\mathbb R^{\vec E(G)}$,
--   $$\bigl|\mathrm{Ov}_{t,\gamma}(G,y)-\mathrm{Ov}_{t,\gamma}(G,y')\bigr|\le C\|y-y'\|.$$
--   Here $\mathrm{Ov}_{t,\gamma}(G,y)$ is the expected overlap of the output of $\mathrm{BP}_{t,\gamma}(G,\beta\sqrt{|\vec E(G)|}\,y)$, $\beta=\frac12\sqrt{1-1/(d\lambda^2)}$.
--
--   It lets BP be initialized at any vector close to the informative eigenvector (Theorem 4.2).
--
--   Differences from the source:
--   - encoding: with high probability → the SBM(n,d,λ) probability of the event tends to 1 (Whp); reason: the meaning of the phrase
--   - encoding: τ_e drawn for each directed edge e → τ drawn for every ordered pair with weight ∏(1+τ_p tanh Y_p)/2; reason: the output depends only on directed edges, so its law is unchanged
--   - reading: sign(BP(·)) with no rule at 0 → sign(0) = +1; reason: BP(∅) = 0 at isolated vertices; the paper fixes no rule and the argument does not depend on it
-- source:
--   Hopkins, Hua, Mohanty, Rajaraman, Steurer, Optimal Robust Community Detection, STOC 2027 submission (manuscript of November 3, 2026, sha256 3d287d5422db7c4a43e74333bda1dbed204af51a25fd9f2c6e875ae03a4dafa1), Lemma 4.5, p.17 (pdf p.19)

import Mathlib
import Definitions.Def_OptRobustCD_Whp
import Definitions.Def_OptRobustCD_BP

namespace OptRobustCD

/-- **Lemma 4.5** (BP is stable under changes to the initialization). Hopkins, Hua, Mohanty,
Rajaraman, Steurer, *Optimal Robust Community Detection*, STOC 2027 submission (manuscript of
November 3, 2026, sha256 3d287d54…), Lemma 4.5, p.17 (pdf p.19).

"Let dλ² > 1 and (G, σ⋆) ∼ SBM(n, d, λ). For every t ⩾ 1 there is C = C(d, λ, t) > 0 such that with
high probability, for all γ ∈ (0, 1) and all `y, y′ ∈ R^{E⃗(G)}`,
`|Ov_{t,γ}(G, y) − Ov_{t,γ}(G, y′)| ⩽ C∥y − y′∥`."

**Formalization Note.** The high-probability event comes first, then `γ, y, y′`. `Ov` uses the
fixed `β = (1/2)√(1 − 1/(dλ²))` of p.16. `d > 0`, `λ ∈ (−1, 1)` are the standing assumptions of
§3.1 (p.12). -/
theorem lemma_4_5 (d lam : ℝ) (hd : 0 < d) (hlam : lam ∈ Set.Ioo (-1 : ℝ) 1)
    (hKS : 1 < d * lam ^ 2) (t : ℕ) (ht : 1 ≤ t) :
    ∃ C : ℝ, 0 < C ∧ Whp d lam (fun n σ G => ∀ γ : ℝ, γ ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ y y' : EVec n, SupportedOn G y → SupportedOn G y' →
        |Ov d lam t γ G σ y - Ov d lam t γ G σ y'| ≤ C * l2 (y - y')) := by sorry

end OptRobustCD
