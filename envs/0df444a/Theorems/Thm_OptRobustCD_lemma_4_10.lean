-- Prove2me | Theorems.Thm_OptRobustCD_lemma_4_10
-- name    : OptRobustCD.lemma_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:52:33.348194+00:00
-- url     : https://prove2.me/theorems/9d401eed-6e96-42ad-b02e-5cfa0973d29f
-- title:
--   Lemma 4.10 — BP outputs from nearby initializations can be coupled: $\mathbb E|\{v:\hat\sigma_v\ne\hat\sigma'_v\}|\le\frac12(\sum_v|B_G(v,t+1)|^3)^{1/2}\|Y-Y'\|$
-- statement:
--   Let $\lambda\in(-1,1)$, let $G$ be a graph on $[n]$, let $t\ge1$ and $\gamma\in(0,1)$, and let $Y,Y'\in\mathbb R^{\vec E(G)}$. Then the outputs $\hat\sigma$ of $\mathrm{BP}_{t,\gamma}(G,Y)$ and $\hat\sigma'$ of $\mathrm{BP}_{t,\gamma}(G,Y')$ can be coupled so that
--   $$\mathbb E\bigl|\{v:\hat\sigma_v\ne\hat\sigma'_v\}\bigr|\le\frac12\Bigl(\sum_{v\in[n]}|B_G(v,t+1)|^3\Bigr)^{1/2}\|Y-Y'\|,\tag{3}$$
--   where $|B_G(v,s)|$ is the number of vertices within distance $s$ of $v$.
--
--   This is the deterministic core of the stability of BP under changes of its initialization (Lemma 4.5).
--
--   Differences from the source:
--   - encoding: the outputs can be coupled → there is a joint law on pairs of labellings with the two output laws as marginals; reason: the meaning of a coupling
--   - encoding: τ_e drawn for each directed edge e → τ drawn for every ordered pair with weight ∏(1+τ_p tanh Y_p)/2; reason: the output depends only on directed edges, so its law is unchanged
--   - reading: sign(BP(·)) with no rule at 0 → sign(0) = +1; reason: BP(∅) = 0 at isolated vertices; the paper fixes no rule and the argument does not depend on it
-- source:
--   Hopkins, Hua, Mohanty, Rajaraman, Steurer, Optimal Robust Community Detection, STOC 2027 submission (manuscript of November 3, 2026, sha256 3d287d5422db7c4a43e74333bda1dbed204af51a25fd9f2c6e875ae03a4dafa1), Lemma 4.10, eq. (3), p.21 (pdf p.23)

import Mathlib
import Definitions.Def_OptRobustCD_BP

namespace OptRobustCD

open scoped Classical

/-- **Lemma 4.10** (BP outputs from nearby scores can be coupled). Hopkins, Hua, Mohanty,
Rajaraman, Steurer, *Optimal Robust Community Detection*, STOC 2027 submission (manuscript of
November 3, 2026, sha256 3d287d54…), Lemma 4.10, eq. (3), p.21 (pdf p.23).

"Let G be a graph on [n], let t ⩾ 1 and γ ∈ (0, 1), and let `Y, Y′ ∈ R^{E⃗(G)}`. Then the outputs σ̂
and σ̂′ of `BP_{t,γ}(G, Y)` and `BP_{t,γ}(G, Y′)` can be coupled so that
`E|{v : σ̂_v ≠ σ̂′_v}| ⩽ (1/2)(Σ_{v∈[n]} |B_G(v, t + 1)|³)^{1/2} ∥Y − Y′∥`."

**Formalization Note.** "Can be coupled" is the existence of a joint law `μ` on pairs of labellings
whose marginals are the two output laws `bpProb`. `λ ∈ (−1, 1)` is the standing assumption of §3.1
(p.12). The statement is deterministic: no SBM. -/
theorem lemma_4_10 (lam : ℝ) (hlam : lam ∈ Set.Ioo (-1 : ℝ) 1) {n : ℕ} (G : SimpleGraph (Fin n))
    (t : ℕ) (ht : 1 ≤ t) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (Y Y' : EVec n)
    (hY : SupportedOn G Y) (hY' : SupportedOn G Y') :
    ∃ μ : (Fin n → Bool) → (Fin n → Bool) → ℝ, (∀ a b, 0 ≤ μ a b) ∧
      (∀ a, ∑ b, μ a b = bpProb G lam t γ Y a) ∧ (∀ b, ∑ a, μ a b = bpProb G lam t γ Y' b) ∧
      ∑ a, ∑ b, μ a b * ((Finset.univ.filter fun v => a v ≠ b v).card : ℝ) ≤
        (1 / 2) * Real.sqrt (∑ v, (ballCard G v (t + 1) : ℝ) ^ 3) * l2 (Y - Y') := by sorry

end OptRobustCD
