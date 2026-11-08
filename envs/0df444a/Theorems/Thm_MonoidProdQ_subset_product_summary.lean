-- Prove2me | Theorems.Thm_MonoidProdQ_subset_product_summary
-- name    : MonoidProdQ.subset_product_summary
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:58:47.359639+00:00
-- url     : https://prove2.me/theorems/9ba368ff-edb5-4ef8-834a-dd2dcf4f3f77
-- title:
--   Proof of Theorem 18: the subset-product summary has essential width at most $\min\{n,\beta_G(M)\}$
-- statement:
--   Let $M$ be a finite commutative aperiodic monoid, $G\subseteq M$ a nonempty alphabet and $n\ge1$. Then the subset products give an incremental summary (Definition 2) of $\mathrm{Prod}_{M,G,n}$ on the promise domain $G^n$, with state set $M$:
--
--   1. initial state $q_\emptyset=1$;
--   2. update maps $\delta_i(p,a)=pa$;
--   3. readout the identity map $M\to M$;
--   4. summary states $s_x(T)=p_x(T)=\prod_{i\in T}x_i$.
--
--   Moreover, this summary has essential width at most $\min\{n,\beta_G(M)\}$: for every $x\in G^n$ and every $T\subseteq[n]$,
--
--   $$|\mathrm{Ess}_x(T)|\le\min\{n,\beta_G(M)\}.$$
--
--   Combined with Theorem 14 this gives the adversary upper bound (14) of Theorem 18.
--
--   Differences from the source:
--   - encoding: $\min\{n,\beta_G(M)\}$ → `(min (n : ℕ∞) (productBreadth G)).toNat`; reason: the minimum is taken in `ℕ∞` first, so it is finite and equals $n$ when $\beta_G(M)=\infty$
--   - encoding: Definition 2's nonempty promise domain $G^n$ → hypothesis `G.Nonempty`; reason: for $n\ge1$, $G^n$ is nonempty exactly when $G$ is; this is Definition 2's standing assumption
--   - encoding: $G\subseteq M$, inputs in $G^n$, $T\subseteq[n]$ → `G : Finset M`, inputs `Fin n → ↥G`, promise domain `Finset.univ`, `T : Finset (Fin n)`; reason: Lean convention; $M$ is finite and positions are 0-based, same instances
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §5.1, p.33, and proof of Theorem 18, p.34

import Definitions.Def_MonoidProdQ_IsAperiodic
import Definitions.Def_MonoidProdQ_productBreadth
import Definitions.Def_MonoidProdQ_prodMap
import Definitions.Def_MonoidProdQ_subsetProd
import Definitions.Def_MonoidProdQ_IncrementalSummary_HasEssWidthLE

namespace MonoidProdQ

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §5.1, p.33 ("Commutativity makes this an order-independent summary, with update
δ(p, a) = pa, and its final state is the desired product") and the proof of Theorem 18, p.34
("The subset-product summary has essential width at most min{n, β_G(M)} by Lemma 20"): for a
finite commutative aperiodic monoid `M`, `G ⊆ M` and `n ≥ 1`, the subset products
`T ↦ pₓ(T)` with initial state `1`, updates `δᵢ(p, a) = pa` and readout the identity form an
incremental summary (Definition 2) of `Prod_{M,G,n}` on all of `Gⁿ`, with state set `M`, and its
essential width is at most `min{n, β_G(M)}`.

**Formalization Note.** `G` is nonempty, so that the promise domain `Gⁿ` is nonempty (Definition 2's
standing assumption; for `n ≥ 1`, `Gⁿ` is nonempty exactly when `G` is). `min{n, β_G(M)}` is computed in `ℕ∞` and then converted to a natural
number; it is finite because `n` is. -/
theorem subset_product_summary {M : Type*} [CommMonoid M] [Fintype M] [DecidableEq M]
    (hM : IsAperiodic M) (G : Finset M) (hG : G.Nonempty) (n : ℕ) (hn : 1 ≤ n) :
    ∃ S : IncrementalSummary (prodMap G n) Finset.univ M,
      S.q0 = 1 ∧ (∀ (i : Fin n) (p : M) (a : G), S.δ i p a = p * (a : M)) ∧ S.g = id ∧
      (∀ (x : Fin n → G) (T : Finset (Fin n)), S.s x T = subsetProd x T) ∧
      S.HasEssWidthLE ((min (n : ℕ∞) (productBreadth G)).toNat : ℝ) := by sorry

end MonoidProdQ
