-- Prove2me | Theorems.Thm_GeoQAC_lemma_3_12
-- name    : GeoQAC.lemma_3_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:31:18.032858+00:00
-- url     : https://prove2.me/theorems/367a90f4-b46d-4c45-b471-96a4b485a40d
-- title:
--   Lemma 3.12 — one product reflection moves observables by at most $2(\sum c_i^2)^{1/2}$
-- statement:
--   Let $R=I-2\Pi$ be a product reflection with support $G$, and let $H_1,\dots,H_k$ be Hermitian operators with $\|H_i\|\le1$. Suppose there are pairwise disjoint sets $A_1,\dots,A_k\subseteq G$ such that $\mathrm{supp}(H_i)\cap G\subseteq A_i$ for every $i$. Then, for any real coefficients $c_1,\dots,c_k$,
--   $$
--   \Big\|\sum_{i=1}^k c_i\,(RH_iR-H_i)\Big\|\le 2\Big(\sum_{i=1}^k c_i^2\Big)^{1/2}.
--   $$
--   Here $\|\cdot\|$ is the operator norm.
--
--   The bound is the norm estimate for the change of the observables caused by a single gate in the hybrid argument of Lemma 3.9.
--
--   Differences from the source:
--   - encoding: $\mathrm{supp}(H_i)\cap G\subseteq A_i$ → $H_i$ is supported on $A_i\cup(V\setminus G)$; reason: equivalent, since supports of tensor-product operators are closed under intersection.
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), Lemma 3.12, p.19

import Mathlib
import Definitions.Def_DHRUniq_IsUnitVec
import Definitions.Def_GeoQAC_IsSupportedOn
import Definitions.Def_GeoQAC_ReflLayer

namespace GeoQAC

open DHRUniq (IsUnitVec)

open scoped Matrix.Norms.L2Operator

/-- **Lemma 3.12** (arXiv:2604.07178, version of 2026-11-03, p.19). Let `R = I − 2Π` be a product
reflection with support `G`, and let `H_1, …, H_k` be Hermitian operators with `‖H_i‖ ≤ 1`. Suppose
there are pairwise disjoint sets `A_1, …, A_k ⊆ G` such that `supp(H_i) ∩ G ⊆ A_i`. Then for any
real coefficients `c_i`, `‖∑_i c_i (R H_i R − H_i)‖ ≤ 2 (∑_i c_i²)^{1/2}`.

**Formalization Note.**
* The paper's index count `h` is renamed `k` (no clash with the grid length). The lemma uses no
  geometry: the qubits are any finite type `V`.
* `supp(H_i) ∩ G ⊆ A_i` is encoded as "`H_i` is supported on `A_i ∪ Gᶜ`", which is equivalent
  (supports are closed under intersection for tensor-product operators).
* `‖·‖` is the L2 operator norm; the one-qubit factors `φ_v`, `v ∈ G`, are unit vectors. -/
theorem lemma_3_12 {V : Type} [Fintype V] [DecidableEq V] (G : Finset V) (φ : V → Bool → ℂ)
    (hφ : ∀ v ∈ G, IsUnitVec (φ v)) {k : ℕ}
    (H : Fin k → Matrix (V → Bool) (V → Bool) ℂ) (hH : ∀ i, (H i).IsHermitian ∧ ‖H i‖ ≤ 1)
    (A : Fin k → Finset V) (hAG : ∀ i, A i ⊆ G)
    (hAdisj : Pairwise fun i j => Disjoint (A i) (A j))
    (hsupp : ∀ i, IsSupportedOn (A i ∪ (Finset.univ \ G)) (H i)) (c : Fin k → ℝ) :
    ‖∑ i, (c i : ℂ) • (productReflection G φ * H i * productReflection G φ - H i)‖ ≤
      2 * Real.sqrt (∑ i, c i ^ 2) := by sorry

end GeoQAC
