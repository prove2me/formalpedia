-- Prove2me | Theorems.Thm_OptRobustCD_lemma_4_6
-- name    : OptRobustCD.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:52:36.224298+00:00
-- url     : https://prove2.me/theorems/f6ab1a9e-ed30-40eb-a17b-c2703e590b9b
-- title:
--   Lemma 4.6 — BP is stable under edge edits: $|\mathrm{Ov}_{t,\gamma}(G',y)-\mathrm{Ov}_{t,\gamma}(G,y|_{\vec E(G)})|\le C\sqrt\eta$
-- statement:
--   Let $d>0$, $\lambda\in(-1,1)$ with $d\lambda^2>1$, and $(G,\sigma^\star)\sim\mathrm{SBM}(n,d,\lambda)$. For every $t\ge1$ there is $C=C(d,\lambda,t)>0$ such that with high probability the following holds for all $\eta,\gamma\in(0,1)$. Let $G'$ be a graph on $[n]$ with $|E(G)\triangle E(G')|\le\eta n$, let $y\in\mathbb R^{\vec E(G')}$ have $\|y\|\le1$, and let $y|_{\vec E(G)}$ be its restriction to $\vec E(G)$. Then
--   $$\bigl|\mathrm{Ov}_{t,\gamma}(G',y)-\mathrm{Ov}_{t,\gamma}(G,y|_{\vec E(G)})\bigr|\le C\sqrt\eta.$$
--
--   It transfers the BP guarantee from the clean graph to the corrupted one (Theorem 4.2).
--
--   Differences from the source:
--   - encoding: with high probability → the SBM(n,d,λ) probability of the event tends to 1 (Whp); reason: the meaning of the phrase
--   - encoding: τ_e drawn for each directed edge e → τ drawn for every ordered pair with weight ∏(1+τ_p tanh Y_p)/2; reason: the output depends only on directed edges, so its law is unchanged
--   - reading: sign(BP(·)) with no rule at 0 → sign(0) = +1; reason: BP(∅) = 0 at isolated vertices; the paper fixes no rule and the argument does not depend on it
-- source:
--   Hopkins, Hua, Mohanty, Rajaraman, Steurer, Optimal Robust Community Detection, STOC 2027 submission (manuscript of November 3, 2026, sha256 3d287d5422db7c4a43e74333bda1dbed204af51a25fd9f2c6e875ae03a4dafa1), Lemma 4.6, p.17 (pdf p.19)

import Mathlib
import Definitions.Def_OptRobustCD_Whp
import Definitions.Def_OptRobustCD_BP

namespace OptRobustCD

/-- **Lemma 4.6** (BP is stable under edge edits). Hopkins, Hua, Mohanty, Rajaraman, Steurer,
*Optimal Robust Community Detection*, STOC 2027 submission (manuscript of November 3, 2026, sha256
3d287d54…), Lemma 4.6, p.17 (pdf p.19).

"Let dλ² > 1 and (G, σ⋆) ∼ SBM(n, d, λ). For every t ⩾ 1 there is C = C(d, λ, t) > 0 such that with
high probability the following holds for all η, γ ∈ (0, 1). Let G′ be a graph on [n] with
|E(G)△E(G′)| ⩽ ηn, let `y ∈ R^{E⃗(G′)}` have ∥y∥ ⩽ 1, and let `y|_{E⃗(G)}` be the restriction of y to
`E⃗(G)` … Then `|Ov_{t,γ}(G′, y) − Ov_{t,γ}(G, y|_{E⃗(G)})| ⩽ C√η`."

**Formalization Note.** The high-probability event comes first, then `η, γ, G′, y`. `d > 0`,
`λ ∈ (−1, 1)` are the standing assumptions of §3.1 (p.12). -/
theorem lemma_4_6 (d lam : ℝ) (hd : 0 < d) (hlam : lam ∈ Set.Ioo (-1 : ℝ) 1)
    (hKS : 1 < d * lam ^ 2) (t : ℕ) (ht : 1 ≤ t) :
    ∃ C : ℝ, 0 < C ∧ Whp d lam (fun n σ G => ∀ η γ : ℝ, η ∈ Set.Ioo (0 : ℝ) 1 →
      γ ∈ Set.Ioo (0 : ℝ) 1 → ∀ G' : SimpleGraph (Fin n), (editDist G G' : ℝ) ≤ η * n →
        ∀ y : EVec n, SupportedOn G' y → l2 y ≤ 1 →
          |Ov d lam t γ G' σ y - Ov d lam t γ G σ (restrictTo G y)| ≤ C * Real.sqrt η) := by sorry

end OptRobustCD
