-- Prove2me | Theorems.Thm_GaussianSweep_lemma_8_4
-- name    : GaussianSweep.lemma_8_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:55:04.479194+00:00
-- url     : https://prove2.me/theorems/5eafcf96-614b-48da-8cab-5b59cc0be415
-- title:
--   Lemma 8.4 — median-switched layout: $\mathrm{pw}(G) \le w$
-- statement:
--   Let $G$ be a finite graph with $\Delta(G) \le 3$, let $y : V(G) \to \mathbb R$ be an injective labeling, and let $w \ge 0$ be a real number such that
--
--   1. $|\partial^- S_t| \le w$ for every $t < 0$;
--   2. $|\partial^+ S_t| \le w$ for every $t > 0$;
--   3. $\max(L_0, L_0') + 1 \le w$, with $L_0 = |U| + |D \cap W|$ and $L_0' = |W| + |D \cap U|$ as in (8.2).
--
--   Then
--   $$
--   \mathrm{pw}(G) \le w .
--   $$
--   This is the deterministic half of Theorem 8.1: it turns small inner frontiers below zero, small outer frontiers above zero and small switching sets at zero into a path decomposition.
--
--   Differences from the source:
--   - encoding: a finite simple graph G → a SimpleGraph on a finite vertex type V (Fintype), n = card V; reason: every finite graph is isomorphic to one on a finite type; pathwidth and degrees are invariant
--   - encoding: pw(G) ≤ w for a real w → (pathwidth G : ℝ) ≤ w, with pathwidth ℤ-valued; reason: the integer is compared with w in ℝ
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Lemma 8.4, p.47 (PDF p.49)

import Mathlib
import Definitions.Def_GaussianSweep_pathwidth
import Definitions.Def_GaussianSweep_innerFrontier
import Definitions.Def_GaussianSweep_outerFrontier
import Definitions.Def_GaussianSweep_L0
import Definitions.Def_GaussianSweep_L0prime

namespace GaussianSweep

/-- Lemma 8.4 (median-switched layout) (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Lemma 8.4, p.47 (PDF p.49)). Let `G` be a graph with
`Δ(G) ≤ 3`, `y : V(G) → ℝ` injective, and `w ≥ 0` real with (i) `|∂⁻S_t| ≤ w` for every `t < 0`;
(ii) `|∂⁺S_t| ≤ w` for every `t > 0`; (iii) `max(L₀, L′₀) + 1 ≤ w`, with `L₀, L′₀` as in (8.2).
Then `pw(G) ≤ w`. -/
theorem lemma_8_4 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hΔ : G.maxDegree ≤ 3) (y : V → ℝ) (hy : Function.Injective y) (w : ℝ) (hw : 0 ≤ w)
    (hi : ∀ t < 0, ((innerFrontier G y t).card : ℝ) ≤ w)
    (hii : ∀ t > 0, ((outerFrontier G y t).card : ℝ) ≤ w)
    (hiii : (max (L0 G y) (L0prime G y) : ℝ) + 1 ≤ w) :
    (pathwidth G : ℝ) ≤ w := by sorry

end GaussianSweep
