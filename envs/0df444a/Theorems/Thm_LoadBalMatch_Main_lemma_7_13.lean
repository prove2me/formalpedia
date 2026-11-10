-- Prove2me | Theorems.Thm_LoadBalMatch_Main_lemma_7_13
-- name    : LoadBalMatch.Main.lemma_7_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:34:26.814191+00:00
-- url     : https://prove2.me/theorems/6ba24ce5-6458-41cd-8b12-7366c3c1e111
-- title:
--   Lemma 7.13 — per-iteration potential drop $\Phi_t^2\le1024(\Phi_t-\Phi_{t+1})\sum_{e\in F(x^{(t)})}x^\star_e$
-- statement:
--   Let $G$ be a graph on the finite set $V$ and $x^\star$ a balanced fractional matching of $G$. Consider one iteration: $H\subseteq G$ is stable, $x$ is a balanced fractional matching on $H$, $M$ is a matching of $G$ whose weight $w(M)$ (eq. (36), for $H$ and $x$) is at least $1/3$ of the weight of every matching of $G$, $T$ is a spanning forest of $\widehat G_H$, $H'$ is any graph with $H\cup M\cup T\subseteq H'\subseteq G$, and $x'$ is a balanced fractional matching on $H'$. With $\Phi=\eta(x)-\eta(G)$, $\Phi'=\eta(x')-\eta(G)$ and $F(x)$ the set of edges of $G$ that violate $x$ (Definition 7.12),
--   $$\Phi^2\ \le\ 1024\,(\Phi-\Phi')\sum_{e\in F(x)}x^\star_e .$$
--
--   The paper writes this as $\Phi_t-\Phi_{t+1}\ge\frac{1}{1024}\cdot\Phi_t^2/\sum_{e\in F(x^{(t)})}x^\star_e$ for iteration $t$ of Algorithms 3 and 4, where $H'$ is the stabilized graph containing $H^{(t)}\cup M^{(t)}\cup T^{(t)}$ (and $R^{(t)}$). It is the recursion that bounds the number of passes.
--
--   Differences from the source:
--   - generalization: iteration t ≥ 1 of Algorithm 3 (and of Algorithm 4, p. 47): x = x^(t) on H = supp(x^(t)), x^(t+1) computed on a graph containing H ∪ M ∪ T → any stable H ≤ G, balanced x on H, 1/3-approximate M, spanning forest T, any H′ with H ∪ M ∪ T ≤ H′ ≤ G and balanced x′ on H′; reason: the proof uses exactly these properties; the iterations of Algorithms 3 and 4 are instances (H^(t) is stable)
--   - reading: Φ_t − Φ_{t+1} ≥ (1/1024)·Φ_t² / Σ_{e∈F(x^(t))} x⋆_e → Φ² ≤ 1024·(Φ − Φ′)·Σ_{e∈F(x)} x⋆_e; reason: the denominator can be 0; the multiplied form is the proof's last display and equals the printed one when the denominator is positive
--   - reading: x⋆ = arg min_{x∈P(G)} η(x) → any balanced fractional matching x⋆ of G; reason: the minimiser need not be unique; the statement is made for every one
--   - encoding: a graph G = (V, E) with n = |V| → a SimpleGraph on a finite type V, edges as Sym2 V, n = Fintype.card V; reason: Lean convention; same instances
-- source:
--   Assadi, Bernstein, Wrzos-Kaminska, Better Bounds for Semi-Streaming Maximum Matching via Load Balancing, STOC 2027 submission (sha256 7cd28a8b…), p. 42, Lemma 7.13

import Mathlib
import Definitions.Def_LoadBalMatch_Main_Matching
import Definitions.Def_LoadBalMatch_Main_Stable
import Definitions.Def_LoadBalMatch_Main_FracMatching
import Definitions.Def_LoadBalMatch_Main_GallaiEdmonds
import Definitions.Def_LoadBalMatch_Main_Violation

namespace LoadBalMatch.Main

theorem lemma_7_13 {V : Type*} [Fintype V] [DecidableEq V] (G H : SimpleGraph V)
    (hH : IsStable G H) (x : Sym2 V → ℝ) (hx : IsBalanced H x) (xs : Sym2 V → ℝ)
    (hxs : IsBalanced G xs) (M : Finset (Sym2 V)) (hM : IsMatchingIn G M)
    (hMapprox : ∀ M', IsMatchingIn G M' →
      ∑ e ∈ M', extWeight H x e ≤ 3 * ∑ e ∈ M, extWeight H x e)
    (T : Finset (Sym2 V)) (hT : IsContractedSpanningForest G H T)
    (H' : SimpleGraph V) (hH'lo : addEdges H ↑(M ∪ T) ≤ H') (hH'G : H' ≤ G)
    (x' : Sym2 V → ℝ) (hx' : IsBalanced H' x') :
    (eta x - etaOpt G) ^ 2 ≤ 1024 * (eta x - eta x') * violMass G H x xs := by sorry

end LoadBalMatch.Main
