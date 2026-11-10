-- Prove2me | Theorems.Thm_OptRobustCD_lemma_4_12
-- name    : OptRobustCD.lemma_4_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:52:37.059111+00:00
-- url     : https://prove2.me/theorems/7359a42f-6f90-4949-b5c4-096d6077bfe1
-- title:
--   Lemma 4.12 — BP only sees nearby edits: a coupling with $|\{v:\hat\sigma_v\ne\hat\sigma'_v\}|\le\sum_{a\in A}|B_G(a,t)|$ almost surely
-- statement:
--   Let $\lambda\in(-1,1)$, let $G$ and $G'$ be graphs on $[n]$, let $t\ge1$ and $\gamma\in(0,1)$, and let $A$ be the set of endpoints of the edges in $E(G)\triangle E(G')$. Let $y\in\mathbb R^{n^2-n}$. Then the outputs $\hat\sigma$ of $\mathrm{BP}_{t,\gamma}(G,y|_{\vec E(G)})$ and $\hat\sigma'$ of $\mathrm{BP}_{t,\gamma}(G',y|_{\vec E(G')})$ can be coupled so that, with probability $1$ over the randomized rounding,
--   $$\bigl|\{v:\hat\sigma_v\ne\hat\sigma'_v\}\bigr|\le\sum_{a\in A}|B_G(a,t)|.$$
--
--   This is the deterministic core of the stability of BP under edge edits (Lemma 4.6).
--
--   Differences from the source:
--   - encoding: coupled so that with probability 1 the bound holds → a joint law on output pairs, with the two output laws as marginals, every pair in whose support satisfies the bound; reason: the meaning of an almost-sure coupling of finite laws
--   - encoding: y ∈ R^{n²−n} → y on all ordered pairs; reason: the diagonal entries are removed by both restrictions
--   - encoding: τ_e drawn for each directed edge e → τ drawn for every ordered pair with weight ∏(1+τ_p tanh Y_p)/2; reason: the output depends only on directed edges, so its law is unchanged
--   - reading: sign(BP(·)) with no rule at 0 → sign(0) = +1; reason: BP(∅) = 0 at isolated vertices; the paper fixes no rule and the argument does not depend on it
-- source:
--   Hopkins, Hua, Mohanty, Rajaraman, Steurer, Optimal Robust Community Detection, STOC 2027 submission (manuscript of November 3, 2026, sha256 3d287d5422db7c4a43e74333bda1dbed204af51a25fd9f2c6e875ae03a4dafa1), Lemma 4.12, p.23 (pdf p.25)

import Mathlib
import Definitions.Def_OptRobustCD_BP

namespace OptRobustCD

open scoped Classical

/-- **Lemma 4.12** (BP only sees nearby edits). Hopkins, Hua, Mohanty, Rajaraman, Steurer,
*Optimal Robust Community Detection*, STOC 2027 submission (manuscript of November 3, 2026, sha256
3d287d54…), Lemma 4.12, p.23 (pdf p.25).

"Let G and G′ be graphs on [n], let t ⩾ 1 and γ ∈ (0, 1), and let A be the set of endpoints of the
edges in E(G)△E(G′). Let `y ∈ R^{n²−n}`. Then the outputs σ̂ of `BP_{t,γ}(G, y|_{E⃗(G)})` and σ̂′ of
`BP_{t,γ}(G′, y|_{E⃗(G′)})` can be coupled so that with probability 1 over the randomized rounding of
the initialization, `|{v : σ̂_v ≠ σ̂′_v}| ⩽ Σ_{a∈A} |B_G(a, t)|`."

**Formalization Note.** "Can be coupled so that with probability 1" is the existence of a joint
law `μ` on pairs of output labellings, with the two output laws as marginals, every pair in whose
support satisfies the bound. `y` is any vector on ordered pairs (its diagonal is removed by the
restrictions). `λ ∈ (−1, 1)` is the standing assumption of §3.1. -/
theorem lemma_4_12 (lam : ℝ) (hlam : lam ∈ Set.Ioo (-1 : ℝ) 1) {n : ℕ}
    (G G' : SimpleGraph (Fin n)) (t : ℕ) (ht : 1 ≤ t) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1)
    (y : EVec n) :
    ∃ μ : (Fin n → Bool) → (Fin n → Bool) → ℝ, (∀ a b, 0 ≤ μ a b) ∧
      (∀ a, ∑ b, μ a b = bpProb G lam t γ (restrictTo G y) a) ∧
      (∀ b, ∑ a, μ a b = bpProb G' lam t γ (restrictTo G' y) b) ∧
      ∀ a b, μ a b ≠ 0 → ((Finset.univ.filter fun v => a v ≠ b v).card : ℝ) ≤
        ∑ x ∈ editEndpoints G G', (ballCard G x t : ℝ) := by sorry

end OptRobustCD
