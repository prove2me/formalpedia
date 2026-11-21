-- Prove2me | Theorems.Thm_MasulloGRH_strictLF_quotient_condM_of_weakQ
-- name    : MasulloGRH.strictLF_quotient_condM_of_weakQ
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T00:07:45.820233+00:00
-- url     : https://prove2.me/theorems/354d7e8e-e61e-467c-9ac3-50372c32575e
-- title:
--   The weak quotient neighborhood condition upgrades to unscaled comparison for nuclear Fréchet stages
-- statement:
--   Let $E$ be the strict countable inductive limit of an increasing sequence of nuclear Fréchet subspaces $X_n$, and let $V$ be a closed subspace of $E$. Put $P_n=X_n/(X_n\cap V)$ and identify each $P_n$ with its canonical image in $E/V$. Write $q$ for the quotient map. Suppose that for each $n$ there exist $m\ge n$ and a zero-neighborhood $U$ in $X_n$ such that for each $k\ge m$ and zero-neighborhood $W$ in $X_m$ there are a zero-neighborhood $O$ in $X_k$ and a scalar $r>0$ with $q(U)\cap q(O)\subseteq r q(W)$. Then for the same $n$, $m$ and $U$ in the argument, the comparison holds with an unscaled target: for every such $k,W$ there is a zero-neighborhood $O'$ in $X_k$ with
--   $$q(U)\cap q(O')\subseteq q(W).$$
--   This is the passage from condition (wQ) to condition (Q) for the quotient spectrum in the limit-subspace problem.
-- source:
--   J. Wengenroth, Acyclic inductive spectra of Fréchet spaces, Studia Math. 120 (1996), pp. 253–254, proof of Theorem 3.3, (5) to (6). https://doi.org/10.4064/sm-120-3-247-258

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem strictLF_quotient_condM_of_weakQ (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hwQ : ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ∃ U ∈ nhds (0 : X n), ∀ k : ℕ, m ≤ k →
      ∀ W ∈ nhds (0 : X m), ∃ U' ∈ nhds (0 : X k), ∃ r : ℝ, 0 < r ∧
        ∀ x ∈ U, ∀ y ∈ U', ((x : E) - (y : E)) ∈ V →
          ∃ w ∈ W, ((x : E) - (r : ℂ) • (w : E)) ∈ V) :
    ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ∃ U ∈ nhds (0 : X n), ∀ k : ℕ, m ≤ k →
      ∀ W ∈ nhds (0 : X m), ∃ W' ∈ nhds (0 : X k),
        ∀ x ∈ U, ∀ y ∈ W', ((x : E) - (y : E)) ∈ V → ∃ w ∈ W, ((x : E) - (w : E)) ∈ V := by sorry

end MasulloGRH
