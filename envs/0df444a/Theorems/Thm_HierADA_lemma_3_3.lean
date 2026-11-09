-- Prove2me | Theorems.Thm_HierADA_lemma_3_3
-- name    : HierADA.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:59:56.020076+00:00
-- url     : https://prove2.me/theorems/f52c3ef3-23c4-4a62-aa90-e6a85dda5386
-- title:
--   Lemma 3.3 — one update and accumulated reference advantage
-- statement:
--   Fix a threshold $\tau>0$ and a block of size $r\ge1$, with value function $\Phi$ (Equation (8)) and weights $w(G)$ (Equation (2)).
--
--   1. For all $G,g\in\mathbb R^r$,
--   $$
--   \Phi(G+g)-\Phi(G)\le\frac\tau4\langle w(G),g\rangle+\frac{\tau^2}{32}\|g\|_\infty^2 .
--   $$
--   2. For every sequence $g^{(1)},\dots,g^{(m)}$, with $G^{(0)}=0$, $G^{(s)}=G^{(s-1)}+g^{(s)}$ and $w^{(s)}=w(G^{(s-1)})$ the weights before update $s$, every fixed $u\in W$ satisfies
--   $$
--   \sum_{s=1}^m\langle u-w^{(s)},g^{(s)}\rangle\le\frac{4R(u)}\tau+\frac\tau8\sum_{s=1}^m\|g^{(s)}\|_\infty^2 .
--   $$
--
--   The second inequality bounds the total advantage of a fixed reference vector over the weights the algorithm maintains, the regret of this follow-the-regularized-leader update. It is the one-block estimate behind the potential argument of Proposition 3.4.
--
--   **Formalization Note** $W$ is the published `NondualOpt.cappedSimplex r 8`. $\|g\|_\infty=\max_i|g_i|$ is Lean's norm on $\mathbb R^r$ as a product space. The sequence is indexed from $0$: $g_s$ for $s<m$ is $g^{(s+1)}$, and the weights before it are $w(\sum_{s'<s}g_{s'})$.
--
--   Differences from the source:
--   - encoding: a block of size r, the threshold τ = α/(4p) → 1 ≤ r and 0 < τ; reason: the lemma's setting: W is empty for r = 0, and the paper's τ is positive
--   - encoding: Φ(G) = max over W → sSup of the objective over W; reason: the maximum is attained for r ≥ 1
--   - encoding: ‖g‖∞ = max_i |g_i|; s = 1, …, m → Lean's sup norm on Fin r → ℝ; 0-based s < m; reason: same quantities
-- source:
--   Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams, preprint (version of 2026-11-03, sha256 f220ae51…), Lemma 3.3, p.20, Equations (9)–(10)

import Mathlib
import Definitions.Def_NondualOpt_cappedSimplex
import Definitions.Def_HierADA_penalty
import Definitions.Def_HierADA_Phi
import Definitions.Def_HierADA_regWeights

set_option autoImplicit false

namespace HierADA

/-- **Lemma 3.3 (One update and accumulated reference advantage)** — Gribelyuk–Lin–Lyu–Majid–Woodruff–
Yu–Zhou, *Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams*, preprint
(version of 2026-11-03, sha256 f220ae51…), Lemma 3.3, p.20, Equations (9) and (10).

For a block of size `r ≥ 1` and a threshold `τ > 0`, with `Φ` of Equation (8) and `w(G)` of
Equation (2):
1. for all `G, g ∈ ℝ^r`, `Φ(G + g) − Φ(G) ≤ (τ/4)⟨w(G), g⟩ + (τ²/32)‖g‖∞²`;
2. for every sequence `g(1), …, g(m)`, with `G(0) = 0`, `G(s) = G(s−1) + g(s)` and
   `w(s) = w(G(s−1))`, every fixed `u ∈ W` satisfies
   `∑_{s=1}^m ⟨u − w(s), g(s)⟩ ≤ 4R(u)/τ + (τ/8) ∑_{s=1}^m ‖g(s)‖∞²`.

**Formalization Note.** `‖g‖` on `Fin r → ℝ` is Lean's sup norm `max_i |g_i|`. The sequence is
0-based: `g s` for `s < m` is the paper's `g(s+1)`, and the weights before it are
`w(∑_{s' < s} g s')`. `r ≥ 1` (the feasible set is empty for `r = 0`) and `τ > 0` (the paper's
`τ = α/(4p)`) are the setting of the lemma. -/
theorem lemma_3_3 (τ : ℝ) (hτ : 0 < τ) (r : ℕ) (hr : 1 ≤ r) :
    (∀ G g : Fin r → ℝ,
      Phi τ r (G + g) - Phi τ r G ≤
        τ / 4 * ∑ i, regWeights τ r G i * g i + τ ^ 2 / 32 * ‖g‖ ^ 2) ∧
    ∀ (m : ℕ) (g : ℕ → Fin r → ℝ) (u : Fin r → ℝ), u ∈ NondualOpt.cappedSimplex r 8 →
      ∑ s ∈ Finset.range m,
          ∑ i, (u i - regWeights τ r (∑ s' ∈ Finset.range s, g s') i) * g s i ≤
        4 * penalty r u / τ + τ / 8 * ∑ s ∈ Finset.range m, ‖g s‖ ^ 2 := by sorry

end HierADA
