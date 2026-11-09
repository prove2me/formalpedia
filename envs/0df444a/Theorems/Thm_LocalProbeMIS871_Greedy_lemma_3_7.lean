-- Prove2me | Theorems.Thm_LocalProbeMIS871_Greedy_lemma_3_7
-- name    : LocalProbeMIS871.Greedy.lemma_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T01:54:24.15131+00:00
-- url     : https://prove2.me/theorems/d41d5b2b-fd16-4ad3-b10d-7e4a783287ec
-- title:
--   Lemma 3.7 — Weighted residual sets and simultaneous extensions
-- statement:
--   Let $G$ be a finite simple undirected labeled graph, let $v$ be its fixed query root, and use the cached, early-stopping greedy evaluation. Write $R$ for its fresh evaluated vertices, $U=|R|$, $\tau(u)$ for elimination times, $M_s=\sum_{u\in R}\tau(u)^s$, $X=\sum_{u\in R\setminus\{v\}}\tau(u)^s$, $D=\sum_{u\in R\setminus\{v\}}\tau(u)^s\ln(r(u)/\tau(u))$, and $c_s=\ln(s-1)-1$. Unless stated otherwise below, the root has rank $1$ and the other ranks are independent uniforms on $(0,1)$.
--
--   Fix $0<a<1$ and any nonnegative Lebesgue integrable weight $\psi$ on $(a,1)$. Let $Z^a(\psi)$ and $\omega_\psi$ be the weighted residual-set sum and product, and let admissibility mean each nonroot vertex has a higher-ranked neighbor in the same set. Then
--
--   $$\int_a^1\psi(z)\,dz\le a\quad\Longrightarrow\quad\mathbb E[Z^a(\psi)]\le1.$$
--
--   For every distinct-rank realization, simultaneously for every admissible $S\subseteq V(H_a)$ containing $v$ and every $B\subseteq V(H_a)\setminus S$ whose vertices each have a higher-ranked neighbor in $S$,
--
--   $$Z^a(\psi)\ge\omega_\psi(S)\prod_{u\in B}(1+\psi(r(u))).$$
--
--   Both the expectation and the simultaneous extension inequality are retained, so the assertion applies to sets chosen after the ranks are sampled.
--
--   Differences from the source:
--   - encoding: finite labeled graph and real rank assignment → Fin n, lexicographic real-rank/label keys, and computed cached execution; reason: zero-based labels enumerate exactly the same finite graphs and implement the source tie rule without adding a hypothesis
--   - encoding: arbitrary nonnegative integrable interval weights and expected weighted sum → nonnegative IntegrableOn weights, zero extension outside (a,1), and a measurable lower Lebesgue integral; reason: every source weight is represented, no weight is evaluated at the root, and exceptional nonroot endpoints have zero probability
-- source:
--   Peter Kiss, Yuichi Yoshida, The Local Probe Complexity of Maximal Independent Set, STOC 2027 submission #871 (October 2026), p. 16, PDF p. 18, Lemma 3.7, Eqs.(13)–(14); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/871.pdf

import Definitions.Def_LocalProbeMIS871_Greedy_Weighted

open MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false

namespace LocalProbeMIS871.Greedy

/-- Lemma 3.7, Eqs.(13)–(14), printed p.16 / PDF18; both conclusions. -/
theorem lemma_3_7 {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    (a : ℝ) (ha : 0 < a ∧ a < 1) (ψ : ℝ → ℝ) (hψ : Weight a ψ) :
    ((∫ z in Set.Ioo a 1, ψ z) ≤ a →
      AEMeasurable (Z G v a ψ) (forcedLaw v) ∧
      (∫⁻ r, ENNReal.ofReal (Z G v a ψ r) ∂forcedLaw v) ≤ 1) ∧
    (∀ r, GoodRanks v r → ∀ S B : Finset (Fin n),
      S ⊆ H G r a → v ∈ S → Adm G v r S →
      B ⊆ H G r a \ S →
      (∀ u ∈ B, ∃ z ∈ S, G.Adj u z ∧ r u < r z) →
      omega v r a ψ S * (∏ u ∈ B, (1 + weightValue a ψ (r u))) ≤ Z G v a ψ r) := by sorry

end LocalProbeMIS871.Greedy
