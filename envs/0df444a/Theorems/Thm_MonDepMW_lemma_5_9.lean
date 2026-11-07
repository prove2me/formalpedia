-- Prove2me | Theorems.Thm_MonDepMW_lemma_5_9
-- name    : MonDepMW.lemma_5_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:49:52.193402+00:00
-- url     : https://prove2.me/theorems/38ff3336-bf27-40f1-87ac-4de27a9fb8c5
-- title:
--   Lemma 5.9 — packing ratio from growth ratio
-- statement:
--   Let $G$ be a graph, $\gamma$ the growth ratio of $\mathcal T_1$ on $G$, and $d$ the maximum of $1$ and the VC dimension of the set system $\{N[u]:u\in V(G)\}$. Then the packing ratio $\beta$ of $G$ satisfies
--   $$\beta\leqslant10d\gamma\leqslant20\gamma\log_2(2\gamma).$$
--
--   Together with Theorem 3.3 it bounds the packing ratio on a monadically dependent class.
--
--   **Formalization Note** The VC dimension is Mathlib's `Finset.vcDim`.
--
--   Differences from the source:
--   - generalization: γ the growth ratio of 𝒯₁ on G → every γ ≥ 1 bounding the growth ratio; reason: at the exact growth ratio (which is ≥ 1 when n ≥ 1) this is the source’s claim; at n = 0 the source’s claim is vacuous
-- source:
--   Dreier, Mählmann, Pilipczuk, Toruńczyk, Monadically Dependent Graph Classes Have Almost Bounded Merge-Width, arXiv:2611.06804 (held version, sha256 6e4b0608…), Lemma 5.9, p.20

import Mathlib
import Definitions.Def_MonDepMW_oneType
import Definitions.Def_MonDepMW_PackingLE

set_option autoImplicit false

namespace MonDepMW

open Classical in
/-- **Lemma 5.9.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), p.20: "Let G be a graph, γ be the growth ratio of 𝒯1 on G, and d be the maximum of 1 and the VC
dimension of the set system {N[u]: u ∈ V (G)}. Then the packing ratio β of G is at most β ⩽ 10dγ ⩽ 20γ log2(2γ)."

**Formalization Note.** Posed for every `γ ≥ 1` bounding the growth ratio; this contains the exact growth ratio when `n ≥ 1`,
and both bounds are monotone in `γ`. `N[u]` is the Finset of `v` with `v = u` or `v` adjacent to `u`. -/
theorem lemma_5_9 {n : ℕ} (G : SimpleGraph (Fin n)) (γ : ℕ) (hγ : 1 ≤ γ)
    (hG : ∀ A : Finset (Fin n), A.Nonempty → numParts (oneType G A) ≤ γ * A.card) (d : ℕ)
    (hd : d = max 1 (Finset.univ.image fun u : Fin n =>
      Finset.univ.filter fun v : Fin n => v = u ∨ G.Adj u v).vcDim) :
    PackingLE G (10 * d * γ) ∧
      (10 * (d : ℝ) * (γ : ℝ)) ≤ 20 * (γ : ℝ) * Real.logb 2 (2 * (γ : ℝ)) := by sorry

end MonDepMW
