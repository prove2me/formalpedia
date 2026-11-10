-- Prove2me | Theorems.Thm_LoadBalMatch_Main_lemma_7_10
-- name    : LoadBalMatch.Main.lemma_7_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:33:17.273559+00:00
-- url     : https://prove2.me/theorems/f3c2ecd0-9c93-4289-b8fb-649dad5b059f
-- title:
--   Lemma 7.10 — if $\Phi\le\varepsilon^2\mu(G)$ then $\mathrm{supp}(x)$ contains a matching of size $\ge(1-\varepsilon)\mu(G)$
-- statement:
--   Let $G$ be a graph on the finite set $V$, $0<\varepsilon<1$, $H\subseteq G$ a subgraph and $x\in P(H)$ a fractional matching, and write $\Phi=\eta(x)-\eta(G)$, where $\eta(G)=\min_{x'\in P(G)}\eta(x')$. If
--   $$\Phi\ \le\ \varepsilon^2\,\mu(G),$$
--   then the support $\operatorname{supp}(x)$ contains a matching of size at least $(1-\varepsilon)\mu(G)$.
--
--   In the paper the lemma is stated for the iterate $x^{(t)}$ of Algorithm 3 with $\Phi_t=\eta(x^{(t)})-\eta^\star$; it converts a small potential into the algorithm's output guarantee.
--
--   Differences from the source:
--   - generalization: x = x^(t), the fractional matching at the start of iteration t of Algorithm 3 (balanced on H^(t)) → any subgraph H ≤ G and any x ∈ P(H), not necessarily balanced; reason: the proof (that of Lemma 4.7) uses only x ∈ P(G); the iterate is an instance
--   - reading: ε, the algorithm's parameter → 0 < ε < 1; reason: the standing range ε ∈ (0, 1) of Theorems 2 and 3
--   - encoding: Φ_t = η(x^(t)) − η⋆ with η⋆ = min_{x′∈P(G)} η(x′) → eta x − etaOpt G; reason: etaOpt G is the attained minimum
--   - encoding: a graph G = (V, E) with n = |V| → a SimpleGraph on a finite type V, edges as Sym2 V, n = Fintype.card V; reason: Lean convention; same instances
-- source:
--   Assadi, Bernstein, Wrzos-Kaminska, Better Bounds for Semi-Streaming Maximum Matching via Load Balancing, STOC 2027 submission (sha256 7cd28a8b…), p. 40, Lemma 7.10

import Mathlib
import Definitions.Def_LoadBalMatch_Main_Matching
import Definitions.Def_LoadBalMatch_Main_FracMatching

namespace LoadBalMatch.Main

theorem lemma_7_10 {V : Type*} [Fintype V] [DecidableEq V] (G H : SimpleGraph V)
    (hHG : H ≤ G) (x : Sym2 V → ℝ) (hx : IsFracMatching H x) (ε : ℝ) (hε0 : 0 < ε)
    (hε1 : ε < 1) (hΦ : eta x - etaOpt G ≤ ε ^ 2 * (matchingNumber G : ℝ)) :
    ∃ M, IsMatchingIn (supportGraph x) M ∧
      (1 - ε) * (matchingNumber G : ℝ) ≤ (M.card : ℝ) := by sorry

end LoadBalMatch.Main
