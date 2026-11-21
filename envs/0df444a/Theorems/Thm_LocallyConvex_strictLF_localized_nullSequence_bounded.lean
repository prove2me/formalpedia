-- Prove2me | Theorems.Thm_LocallyConvex_strictLF_localized_nullSequence_bounded
-- name    : LocallyConvex.strictLF_localized_nullSequence_bounded
-- status  : Proved
-- author  : @ibecca
-- created : 2026-11-21T00:13:25.098574+00:00
-- url     : https://prove2.me/theorems/692d9333-b8dd-422a-9f51-b326af4e1cbe
-- title:
--   Null-sequence images are bounded in a localized Frechet quotient stage
-- statement:
--   Let $E$ be the strict countable locally convex inductive limit of its increasing Frechet subspaces $X_n$, let $V$ be closed, and write $q:E\to Q=E/V$. Let $P_m=q(X_m)$ carry the quotient topology inherited from $X_m$, rather than the subspace topology of $Q$. Assume that each $X_n$ has a zero-neighborhood $U$ such that the closure of $q(U)$ in $Q$ is contained in some $P_j$.
--
--   For every $n$ there are $m\ge n$ and a zero-neighborhood $U\subseteq X_n$ with the following property. Whenever $k\ge m$, a sequence $(y_i)$ tends to zero in $X_k$, and $q(y_i)\in q(U)$ for every $i$, the sequence $(q(y_i))$ is bounded in $P_m$. Explicitly, for every zero-neighborhood $W\subseteq X_m$ there exists $R>0$ such that
--
--   $$\forall r\ge R\;\forall i\in\mathbb N\;\exists w\in W,\qquad y_i-rw\in V.$$
--
--   This separates the bounded-disk transport step from the first-countability argument giving the uniform neighborhood estimate in condition $(wQ)$. It is an intermediate consequence reconstructed from the Banach-disk and closed-graph argument described for the localized-closure frontier, not a verbatim theorem of the cited paper. Its formal proof remains an open obligation. In particular, boundedness is required in the quotient-stage topology, not merely in $Q$.
-- source:
--   Intermediate Banach-disk transport consequence reconstructed for MasulloGRH.strictLF_quotient_weakQ_of_localized_closures (https://prove2.me/theorems/7ad5fd90-01d7-4a76-8925-16bcc59888a9). Source context: J. Wengenroth, Acyclic inductive spectra of Frechet spaces, Studia Mathematica 120 (1996), 247-258, Proposition 3.2, pp. 252-253, DOI 10.4064/sm-120-3-247-258. The intermediate statement is not a quotation; it isolates the Banach-disk/closed-graph step of the argument.

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false
open MasulloGRH

theorem LocallyConvex.strictLF_localized_nullSequence_bounded
    (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hloc : ∀ n : ℕ, ∃ U ∈ nhds (0 : X n), ∃ j : ℕ,
      closure ((fun x : X n => V.mkQ (x : E)) '' U) ⊆
        Set.range (Submodule.mapQ (V.comap (X j).subtype) V (X j).subtype le_rfl)) :
    ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ∃ U ∈ nhds (0 : X n),
      ∀ k : ℕ, m ≤ k → ∀ y : ℕ → X k,
        Filter.Tendsto y Filter.atTop (nhds (0 : X k)) →
        (∀ i, ∃ x ∈ U, ((x : E) - (y i : E)) ∈ V) →
        ∀ W ∈ nhds (0 : X m), ∃ R : ℝ, 0 < R ∧
          ∀ r : ℝ, R ≤ r → ∀ i, ∃ w ∈ W,
            ((y i : E) - (r : ℂ) • (w : E)) ∈ V := by sorry
