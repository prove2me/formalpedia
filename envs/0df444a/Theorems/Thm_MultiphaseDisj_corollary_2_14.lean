-- Prove2me | Theorems.Thm_MultiphaseDisj_corollary_2_14
-- name    : MultiphaseDisj.corollary_2_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:29:10.664948+00:00
-- url     : https://prove2.me/theorems/040d6ff5-9578-49e1-adb6-ddebc50a96b4
-- title:
--   Corollary 2.14 — flat decomposition of rectangles
-- statement:
--   Let $\mathcal S$ be a finite family of sets, $d\ge0$ real, let $\mu$ be a $d$-rectangle on $\mathcal S\times\mathcal S$, and let $K$ be an integer with $1\le K\le2^{-d}|\mathcal S|$. Then there are subfamilies $A_j,B_k\subseteq\mathcal S$ of size $K$ and weights $p_j,q_k\ge0$ with $\sum_jp_j=\sum_kq_k=1$ such that
--   $$
--   \mu=\sum_{j,k}p_jq_k\,U_{A_j\times B_k}.
--   $$
--
--   Every $d$-rectangle is thus a convex combination of uniform distributions on combinatorial rectangles of size about $2^{-d}|\mathcal S|$, which reduces the min-entropy form of the corruption bound to the combinatorial one.
--
--   **Formalization Note** The families of $A_j$ and of $B_k$ are indexed by finite sets; $U_{A\times B}=U_A\otimes U_B$.
--
--   Differences from the source:
--   - encoding: subfamilies A_j, B_k indexed by unspecified index sets → finite index sets Fin J, Fin L; reason: a convex combination is finite
--   - encoding: a finite family S of sets → a finite family of finite subsets of a finite type; reason: same instances
--   - encoding: d ≥ 0 (Definition 2.13) → not assumed; reason: a deficit is nonnegative, so it follows from the d-rectangle hypothesis
-- source:
--   Ko, Unconditional Boolean Dynamic Lower Bounds from Disjointness, arXiv:2610.10904 (held version, sha256 ba26649b…), Corollary 2.14, p.14

import Mathlib
import Definitions.Def_MultiphaseDisj_Rectangle

set_option autoImplicit false

namespace MultiphaseDisj

/-- **Corollary 2.14 (Flat decomposition of rectangles)** (Ko, *Unconditional Boolean Dynamic Lower Bounds from Disjointness*, arXiv:2610.10904, held
version sha256 ba26649b…, Corollary 2.14, p.14). Let `μ` be
a `d`-rectangle on `S × S`, and let `K` be an integer with `1 ≤ K ≤ 2^{−d} |S|`. Then there are
subfamilies `A_j, B_k ⊆ S` of size `K` and weights `p_j, q_k ≥ 0` with
`Σ_j p_j = Σ_k q_k = 1` such that `μ = Σ_{j,k} p_j q_k U_{A_j × B_k}`.

**Formalization Note** The index sets are finite (`Fin J`, `Fin L`); `U_{A × B} = U_A ⊗ U_B` is the
uniform distribution on `A × B` (p.14). Sets are finite subsets of a finite type `α`. The standing
`d ≥ 0` of Definition 2.13 is not assumed: a deficit is nonnegative, so it follows from `IsRect`. -/
theorem corollary_2_14 {α : Type*} [Fintype α] (S : Finset (Finset α)) (d : ℝ)
    (μ : Finset α × Finset α → ℝ) (hμ : IsRect S d μ) (K : ℕ) (hK1 : 1 ≤ K)
    (hK : (K : ℝ) ≤ (2 : ℝ) ^ (-d) * S.card) :
    ∃ (J L : ℕ) (A : Fin J → Finset (Finset α)) (B : Fin L → Finset (Finset α))
      (p : Fin J → ℝ) (q : Fin L → ℝ),
      (∀ j, A j ⊆ S ∧ (A j).card = K) ∧ (∀ k, B k ⊆ S ∧ (B k).card = K) ∧
      (∀ j, 0 ≤ p j) ∧ (∀ k, 0 ≤ q k) ∧ ∑ j, p j = 1 ∧ ∑ k, q k = 1 ∧
      μ = fun x => ∑ j, ∑ k, p j * q k * prodDist (unif (A j)) (unif (B k)) x := by sorry

end MultiphaseDisj
