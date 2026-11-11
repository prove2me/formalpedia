-- Prove2me | Theorems.Thm_IterRoundKMedian_Main_lemma_4_6
-- name    : IterRoundKMedian.Main.lemma_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:27:28.377962+00:00
-- url     : https://prove2.me/theorems/d29fd3a5-ae05-4ea1-805c-ae7f4bc0efbb
-- title:
--   Lemma 4.6 — the one-step saving is at least a quarter of the dispersion: Γ ≥ D(U)/4
-- statement:
--   Let $U$ be a finite set of facilities with openings $y_i\ge0$, $y(U)\le1$, distances $d_i\ge0$, and weights $0\le w_{qi}\le y_q$ for $q,i\in U$. With $V(U)$, $D(U)$, $w(U,i)$, $u_{qi}$, $r_i$, $I$ and $\Gamma$ as in `SinglePivot`,
--   $$\Gamma\ \ge\ \frac{D(U)}{4}\qquad\text{and in particular}\qquad \Gamma\ge0.$$
--
--   $\Gamma$ is the expected one-step decrease (times $|z|_1$) of the potential $\Phi(U,b)=2V(U)+(1-y(U))b$ in the single-pivot rounding (Lemma 4.4); this lemma turns it into a decrease proportional to the dispersion, which is what lets the analysis go below factor 2 for dispersed clients. Lemma 6.7 applies it with $y_q=\delta$ and $u_{qi}=\delta-w_{qi}$ ((65)).
--
--   Differences from the source:
--
--   - generalization: U ⊆ T ⊆ F_j fractional facilities of the current iteration (0 < y_i < 1, y(U) ≤ 1), w the nearest-unit weights of z with 0 ≤ w_qi ≤ z_q = y_q, d_i = d(i, j) → any finite U, y_i ≥ 0 with y(U) ≤ 1, d_i ≥ 0, and any w with 0 ≤ w_qi ≤ y_q for q, i ∈ U; reason: the proof on p. 33 uses only these properties; the iteration's quantities satisfy them, and so does the instance (65) used in Lemma 6.7
--   - encoding: r_i ∈ ℝ ∪ {∞} with min ∅ = ∞ and (y(U) − w(U,i)) r_i := 0 when r_i = ∞ → r_i : WithTop ℝ (Finset.inf over the empty set is ⊤) and mulTopZero c ⊤ = 0; reason: the page's convention
-- source:
--   Byrka, Guo, Hu, Li, Shin, Vajanopath, Wan, Wang, Iterative Randomized Rounding for k-Median in General and Euclidean Metrics, STOC 2027 submission (manuscript sha256 02f6267b…), p. 32, Lemma 4.6

import Mathlib
import Definitions.Def_IterRoundKMedian_Main_SinglePivot

namespace IterRoundKMedian.Main

open SinglePivot in
theorem lemma_4_6 {ι : Type*} (U : Finset ι) (y d : ι → ℝ) (w : ι → ι → ℝ)
    (hy : ∀ i ∈ U, 0 ≤ y i) (hyU : yU U y ≤ 1) (hd : ∀ i ∈ U, 0 ≤ d i)
    (hw_nonneg : ∀ q ∈ U, ∀ i ∈ U, 0 ≤ w q i)
    (hw_le : ∀ q ∈ U, ∀ i ∈ U, w q i ≤ y q) :
    D U y d / 4 ≤ Gamma U y d w ∧ 0 ≤ Gamma U y d w := by sorry

end IterRoundKMedian.Main
