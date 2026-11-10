-- Prove2me | Theorems.Thm_MinSumDimRed_Doubling_lemma_3_4
-- name    : MinSumDimRed.Doubling.lemma_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:34:35.154111+00:00
-- url     : https://prove2.me/theorems/49786f57-2cde-4757-8b9b-b00aeb140c14
-- title:
--   Lemma 3.4 — sparse graph preservation: a $\theta$-everywhere-sparse distortion graph preserves total pairwise distance within $(1+5\theta)(1+2\varepsilon)$ both ways
-- statement:
--   **Lemma 3.4** (Sparse Graph Preservation, p. 11). Let $\theta \le 1/10$, $0 < \varepsilon \le 1/2$, $Y \subseteq \mathbb R^d$ finite, $f : \mathbb R^d \to \mathbb R^t$ any map, and $G = (Y, E)$ the distortion graph of $Y$ for $f$ (an edge $(x, y)$ whenever $\|f(x) - f(y)\| \notin (1 \pm \varepsilon)\|x - y\|$). If $G$ is $\theta$-everywhere sparse, then
--   $$\sum_{x, y \in Y} \|f(x) - f(y)\| \le (1 + 5\theta)(1 + 2\varepsilon) \sum_{x, y \in Y} \|x - y\| \quad (2)$$
--   and
--   $$\sum_{x, y \in Y} \|x - y\| \le (1 + 5\theta)(1 + 2\varepsilon) \sum_{x, y \in Y} \|f(x) - f(y)\| \quad (3),$$
--   sums over ordered pairs.
--
--   Differences from the source:
--   - encoding: Y (a finite point set) and its distortion graph G = (Y, E) → Y : Finset (Pt d); G is distortionGraph ε f induced on Y, and 'G is θ-everywhere sparse' is IsEverywhereSparseOn (distortionGraph ε f) Y θ; reason: the distortion graph of Y is the subgraph of the graph on ℝ^d induced on Y; sums over Y require Y finite, as the paper's |Y| does
--   - reading: a ∈ (1 ± ε) b → WithinFactor ε a b, i.e. (1 − ε)·b ≤ a ∧ a ≤ (1 + ε)·b (closed interval); reason: the paper does not say open or closed; the closed interval is the standard meaning and both inequalities are kept
-- source:
--   Asaf Dallal, Robert Krauthgamer, Dimension Reduction and Coresets for Min-Sum k-Clustering, arXiv:2610.38920 (version of November 2, 2026, SHA-256 13a9281e…), p. 11 (PDF 11), Lemma 3.4 (proof p. 12)

import Mathlib
import Definitions.Def_MinSumDimRed_Doubling_Costs

namespace MinSumDimRed.Doubling

/-- Lemma 3.4 (Sparse Graph Preservation), p. 11: let `θ ≤ 1/10`, `0 < ε ≤ 1/2`, and let
`G = (Y, E)` be the distortion graph of the finite set `Y ⊆ ℝ^d` for a map `f : ℝ^d → ℝ^t`. If
`G` is `θ`-everywhere sparse, then (2) `∑_{x,y∈Y} ‖f(x) - f(y)‖ ≤ (1 + 5θ)(1 + 2ε) ∑_{x,y∈Y} ‖x - y‖`
and (3) `∑_{x,y∈Y} ‖x - y‖ ≤ (1 + 5θ)(1 + 2ε) ∑_{x,y∈Y} ‖f(x) - f(y)‖`. -/
theorem lemma_3_4 {d t : ℕ} (θ ε : ℝ) (hθ : θ ≤ 1 / 10) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (Y : Finset (Pt d)) (f : Pt d → Pt t)
    (hsparse : IsEverywhereSparseOn (distortionGraph ε f) Y θ) :
    (∑ x ∈ Y, ∑ y ∈ Y, ‖f x - f y‖ ≤
        (1 + 5 * θ) * (1 + 2 * ε) * ∑ x ∈ Y, ∑ y ∈ Y, ‖x - y‖) ∧
      (∑ x ∈ Y, ∑ y ∈ Y, ‖x - y‖ ≤
        (1 + 5 * θ) * (1 + 2 * ε) * ∑ x ∈ Y, ∑ y ∈ Y, ‖f x - f y‖) := by sorry

end MinSumDimRed.Doubling
