-- Prove2me | Theorems.Thm_NestedLogitAssort_DeltaGrid_window_level_exists
-- name    : NestedLogitAssort.DeltaGrid.window_level_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:10:04.989573+00:00
-- url     : https://prove2.me/theorems/c39cc733-4e76-49f5-9ff1-b80208608cdb
-- title:
--   Proof of Theorem 12: a nonempty assortment lies in the window of a level of the range
-- statement:
--   Fix $\delta>1$ and a nest $i$ with nonnegative weights $v_{i0}$, $v_{ij}$, and let $V_i(S)=v_{i0}+\sum_{j\in S}v_{ij}$. For every nonempty assortment $S\subseteq N$ with $V_i(S)>0$ there is an integer level $l$ with $l^L_i\le l\le l^U_i$ such that
--
--   $$
--   \delta^{l-1}\le V_i(S)\le\delta^l .
--   $$
--
--   Here $l^L_i=\min\{l\in\mathbb Z:\delta^l\ge v_{i0}+\min_jv_{ij}\}$ and $l^U_i=\min\{l\in\mathbb Z:\delta^l\ge v_{i0}+\sum_jv_{ij}\}$. In the proof of Theorem 12 this level is the one whose assortment $\hat S_{il}$ is compared with $S$; in particular problem (15) is feasible at that level.
--
--   Differences from the source:
--   - reading: v_i0, v_ij are preference weights (p. 7 allows v_i0 = 0 and padding products with v_ij = 0) → hypotheses 0 ≤ v_i0, 0 ≤ v_ij for the nest considered (zero allowed); reason: preference weights of a logit model are nonnegative; the remarks on p. 7 allow exactly the zero values
--   - reading: levels l = l^L_i, …, l^U_i with l^L_i = min{l ∈ Z : δ^l ≥ v^L_i}, l^U_i = min{l ∈ Z : δ^l ≥ v^U_i} → InLevelRange: (∃ j, v_i0 + v_ij ≤ δ^l) ∧ δ^(l−1) < v^U_i, the defining inequalities of the two minima; reason: equal to l^L_i ≤ l ≤ l^U_i whenever v^L_i > 0; when v^L_i = 0 (v_i0 = 0 and a zero-weight product, allowed on p. 7) the printed minimum l^L_i does not exist and every l ≤ l^U_i is admitted, and only finitely many of these levels have (15) feasible; when v^U_i = 0 or n = 0 no level is in range
--   - reading: case S_i ≠ ∅: fix l = l^L_i, …, l^U_i with δ^(l−1) ≤ V_i(S_i) ≤ δ^l → hypotheses S nonempty and 0 < V_i(S); reason: for S_i ≠ ∅ the page uses v^L_i ≤ V_i(S_i), so V_i(S_i) > 0 whenever v^L_i > 0, i.e. whenever l^L_i is defined; a nonempty S with V_i(S) = 0 (v_i0 = 0 and zero-weight products, e.g. one product with v_i1 = 0) lies in no window since δ^(l−1) > 0, and that case is covered by constraint_zero_weight through T(S, ·) = T(∅, ·)
--   - generalization: the step is made inside the setting of Theorem 12 (revenues, γ_i, γ̄ > 1) → only δ > 1 and the weights of nest i are assumed; reason: the existence of the level depends only on the weights and δ; the statement specializes to the page
--   - encoding: δ^l, δ^(l−1) for l ∈ Z and the factors δ^(2γ̄+1), δ^(γ̄+1), δ^(−[a]^+) → zpow for the integer powers, Real.rpow for the real exponents, [a]^+ as max a 0; reason: Lean convention; same values
--   - encoding: products N = {1, …, n}, nests M = {1, …, m} → products Fin n (index 0 is product 1), nests a Fintype M; reason: Lean convention; same instances
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, proof of Theorem 12 (Appendix A.6), case S_i ≠ ∅, p. 53; p. 28

import Mathlib
import Definitions.Def_NestedLogitAssort_DeltaGrid_Window
import Definitions.Def_NestedLogitAssort_DeltaGrid_InLevelRange

namespace NestedLogitAssort.DeltaGrid

/-- **Every nonempty assortment of positive weight lies in the window of a level of the range.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, proof of Theorem 12 (Appendix A.6), case `S_i ≠ ∅`, p. 53 (unnumbered): "Fix
`l = l^L_i, …, l^U_i` such that `δ^{l−1} ≤ v_{i0} + ∑_{j∈S_i} v_{ij} ≤ δ^l`", using
`[v^L_i, v^U_i] ⊂ [δ^{l^L_i − 1}, δ^{l^U_i}]` (p. 28).

For `δ > 1` and nonnegative weights of nest `i`, every nonempty `S` with `V_i(S) > 0` has a
level `l` in the range `l^L_i, …, l^U_i` with `δ^{l−1} ≤ V_i(S) ≤ δ^l`.

**Formalization Note.** The range is `InLevelRange`. The hypothesis `0 < V_i(S)` excludes only
nonempty assortments of zero total weight, which exist only when `v^L_i = 0` (where the printed
`l^L_i` is undefined) and for which no window contains `V_i(S) = 0`. -/
theorem window_level_exists {M : Type*} {n : ℕ} (I : Instance M n) (i : M)
    (hw0 : 0 ≤ I.w0 i) (hv : ∀ j, 0 ≤ I.v i j) (δ : ℝ) (hδ : 1 < δ)
    (S : Finset (Fin n)) (hS : S.Nonempty) (hpos : 0 < V I i S) :
    ∃ l : ℤ, InLevelRange I δ i l ∧ Window I δ i l S := by sorry

end NestedLogitAssort.DeltaGrid
