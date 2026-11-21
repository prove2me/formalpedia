-- Prove2me | Theorems.Thm_MasulloGRH_strictLF_quotient_weakQ_of_localized_closures
-- name    : MasulloGRH.strictLF_quotient_weakQ_of_localized_closures
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T00:04:48.000358+00:00
-- url     : https://prove2.me/theorems/7ad5fd90-01d7-4a76-8925-16bcc59888a9
-- title:
--   The weak condition (wQ) from localization of closures in a Fréchet quotient spectrum
-- statement:
--   Let $E$ be the strict countable locally convex inductive limit of increasing Fréchet subspaces $X_n$, let $V$ be closed, and write $q:E\to Q=E/V$ and $P_j=q(X_j)$, equipped with the quotient topology of $X_j$. Suppose every stage $X_n$ has a zero-neighborhood $U$ for which $\overline{q(U)}^{Q}$ is contained in some $P_j$.
--
--   Then the quotient stages satisfy Vogt’s weak condition $(wQ)$. For every $n$ there exist $m\ge n$ and a zero-neighborhood $U$ of $X_n$ such that for each $k\ge m$ and each zero-neighborhood $W$ of $X_m$, some zero-neighborhood $U'$ of $X_k$ and some $r>0$ satisfy
--   $$
--   q(U)\cap q(U')\subseteq r\,q(W).
--   $$
--
--   This isolates the second part of Wengenroth’s proof of Proposition 3.2. Shrink the chosen $U$ to be absolutely convex and take $m\ge\max(n,j)$. If the conclusion failed for some $k,W$, pass to an absolutely convex zero-neighborhood inside $q(W)$ and use a decreasing zero-basis in $P_k$ to choose $y_i\to0$ in $P_k$ with $y_i\in q(U)$ and $y_i\notin i\,q(W)$ for positive integers $i$. The closed absolutely convex hull of this sequence in the Fréchet space $P_k$ is a bounded Banach disk. It lies in $P_m$ by the closure hypothesis, and the inclusion of its Banach span into $P_m$ has closed graph because both maps to the Hausdorff space $Q$ agree. Consequently the sequence is bounded in $P_m$, contradicting its construction.
-- source:
--   J. Wengenroth, Acyclic inductive spectra of Fréchet spaces, Studia Mathematica 120 (1996), 247–258, https://matwbn.icm.edu.pl/ksiazki/sm/sm120/sm12035.pdf; Definition 3.1 and Proposition 3.2, pp. 252–253

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem strictLF_quotient_weakQ_of_localized_closures
    (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hloc : ∀ n : ℕ, ∃ U ∈ nhds (0 : X n), ∃ j : ℕ,
      closure ((fun x : X n => V.mkQ (x : E)) '' U) ⊆
        Set.range (Submodule.mapQ (V.comap (X j).subtype) V (X j).subtype le_rfl)) :
    ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ∃ U ∈ nhds (0 : X n), ∀ k : ℕ, m ≤ k →
      ∀ W ∈ nhds (0 : X m), ∃ U' ∈ nhds (0 : X k), ∃ r : ℝ, 0 < r ∧
        ∀ x ∈ U, ∀ y ∈ U', ((x : E) - (y : E)) ∈ V →
          ∃ w ∈ W, ((x : E) - (r : ℂ) • (w : E)) ∈ V := by sorry

end MasulloGRH
