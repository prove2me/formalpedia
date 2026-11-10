-- Prove2me | Theorems.Thm_OptRobustCD_lemma_4_4
-- name    : OptRobustCD.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:52:53.637332+00:00
-- url     : https://prove2.me/theorems/0e4f15ee-87c2-4c9b-ab1e-e75ace35f226
-- title:
--   Lemma 4.4 — BP initialized from a constant-depth walk score is near-optimal: $\mathrm{Ov}_{t,\gamma_\ell}(G,\pm W^{(\ell)}/\|W^{(\ell)}\|)\ge\mathrm{OPT}_{d,\lambda}-\varepsilon$
-- statement:
--   Let $d>0$, $\lambda\in(-1,1)$ with $d\lambda^2>1$, and $(G,\sigma^\star)\sim\mathrm{SBM}(n,d,\lambda)$. For every $\varepsilon>0$ there is $t=t(d,\lambda,\varepsilon)\ge1$ such that for every $\ell\ge0$, with high probability,
--   $$\mathrm{Ov}_{t,\gamma_\ell}\bigl(G,W^{(\ell)}/\|W^{(\ell)}\|\bigr)\ge\mathrm{OPT}_{d,\lambda}-\varepsilon\quad\text{and}\quad \mathrm{Ov}_{t,\gamma_\ell}\bigl(G,-W^{(\ell)}/\|W^{(\ell)}\|\bigr)\ge\mathrm{OPT}_{d,\lambda}-\varepsilon.$$
--   Here $\mathrm{OPT}_{d,\lambda}=\lim_t\mathbb E|M_t|$ is the tree quantity of §3.3, $\gamma_\ell$ and $\beta$ are as on p.16, and $W^{(\ell)}$ is the walk score.
--
--   It is the step of Theorem 4.2 that compares BP on the block model with optimal reconstruction on the broadcast tree.
--
--   Differences from the source:
--   - encoding: OPT_{d,λ} = lim_t E|M_t| → treeOPT = inf_t E|M_t|; reason: E|M_t| is nonincreasing (p.14), so the limit is the infimum
--   - encoding: with high probability → the SBM(n,d,λ) probability of the event tends to 1 (Whp); reason: the meaning of the phrase
--   - encoding: τ_e drawn for each directed edge e → τ drawn for every ordered pair with weight ∏(1+τ_p tanh Y_p)/2; reason: the output depends only on directed edges, so its law is unchanged
--   - reading: sign(BP(·)) with no rule at 0 → sign(0) = +1; reason: BP(∅) = 0 at isolated vertices; the paper fixes no rule and the argument does not depend on it
--   - encoding: quotients the source writes only where they are defined → Lean's x/0 = 0 at a zero denominator; reason: changes no instance where the source's quotient is defined; on the high-probability event the denominators are nonzero
-- source:
--   Hopkins, Hua, Mohanty, Rajaraman, Steurer, Optimal Robust Community Detection, STOC 2027 submission (manuscript of November 3, 2026, sha256 3d287d5422db7c4a43e74333bda1dbed204af51a25fd9f2c6e875ae03a4dafa1), Lemma 4.4, p.17 (pdf p.19)

import Mathlib
import Definitions.Def_OptRobustCD_Whp
import Definitions.Def_OptRobustCD_BP
import Definitions.Def_OptRobustCD_treeOPT

namespace OptRobustCD

/-- **Lemma 4.4** (BP initialized from constant-depth walk score is near-optimal). Hopkins, Hua,
Mohanty, Rajaraman, Steurer, *Optimal Robust Community Detection*, STOC 2027 submission
(manuscript of November 3, 2026, sha256 3d287d54…), Lemma 4.4, p.17 (pdf p.19).

"Let dλ² > 1 and (G, σ⋆) ∼ SBM(n, d, λ). For every ε > 0 there is t = t(d, λ, ε) ⩾ 1 such that for
every ℓ ⩾ 0, with high probability, `Ov_{t,γ_ℓ}(G, W^{(ℓ)}/∥W^{(ℓ)}∥) ⩾ OPT_{d,λ} − ε` and the same
holds for `−W^{(ℓ)}/∥W^{(ℓ)}∥`."

**Formalization Note.** `OPT_{d,λ}` here is the tree quantity of §3.3 (`treeOPT`), `γ_ℓ` and `β`
are those of p.16 (`gammaEll`, `betaKS`). `t` is chosen before `ℓ`. `d > 0`, `λ ∈ (−1, 1)` are the
standing assumptions of §3.1 (p.12). -/
theorem lemma_4_4 (d lam : ℝ) (hd : 0 < d) (hlam : lam ∈ Set.Ioo (-1 : ℝ) 1)
    (hKS : 1 < d * lam ^ 2) (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℕ, 1 ≤ t ∧ ∀ ℓ : ℕ, Whp d lam (fun n σ G =>
      treeOPT d lam - ε ≤ Ov d lam t (gammaEll d lam ℓ) G σ
          (fun p => walkScore d lam ℓ G σ p / l2 (walkScore d lam ℓ G σ)) ∧
      treeOPT d lam - ε ≤ Ov d lam t (gammaEll d lam ℓ) G σ
          (fun p => -(walkScore d lam ℓ G σ p / l2 (walkScore d lam ℓ G σ)))) := by sorry

end OptRobustCD
