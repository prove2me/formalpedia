-- Prove2me | Theorems.Thm_MasulloGRH_strictLF_subspace_bornological_of_quotient_weakQ
-- name    : MasulloGRH.strictLF_subspace_bornological_of_quotient_weakQ
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-20T23:58:46.059751+00:00
-- url     : https://prove2.me/theorems/7221bf99-1607-4408-b492-61ad77fa3ff1
-- title:
--   Bornologicity of a closed subspace from weak condition (wQ) on its quotient spectrum
-- statement:
--   Let $E$ be the strict countable locally convex inductive limit of increasing Fréchet subspaces $E_n$, and let $V$ be closed in $E$. Write $q:E\to E/V$ for the quotient map and $P_n=E_n/(E_n\cap V)$. Identify $P_n$ with its image as a vector subspace of $E/V$, keeping the quotient topology of $E_n$ on $P_n$.
--
--   Assume additionally that every stage $E_n$ is nuclear and that $(P_n)$ satisfies $(wQ)$. Then $V$, with the topology induced from $E$, is bornological. Thus every seminorm on $V$ bounded on each bounded subset of $V$ is continuous.
--
--   Vogt’s condition $(wQ)$ for the quotient spectrum means that for each $n$ there are $m\ge n$ and a zero-neighborhood $U\subset E_n$ such that, for each $k\ge m$ and each zero-neighborhood $W\subset E_m$, there are a zero-neighborhood $U'\subset E_k$ and a number $r>0$ satisfying
--   $$
--   q(U)\cap q(U')\subseteq r\,q(W).
--   $$
--   The stage quotient maps are open, so choosing zero-neighborhoods before passing to the quotients gives the same condition.
--
--   This is the subspace application of the criterion. Under these hypotheses the $E_n$ are Fréchet–Schwartz spaces. Wengenroth’s Corollary 3.4 identifies the induced topology on $V$ with the locally convex inductive limit of the stages $E_n\cap V$. These closed stages are metrizable, and a locally convex inductive limit of bornological spaces is bornological.
-- source:
--   J. Wengenroth, Acyclic inductive spectra of Fréchet spaces, Studia Mathematica 120 (1996), 247–258, https://matwbn.icm.edu.pl/ksiazki/sm/sm120/sm12035.pdf; Theorem 3.3 and Corollary 3.4, pp. 253–254

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem strictLF_subspace_bornological_of_quotient_weakQ
    (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hwQ : ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ∃ U ∈ nhds (0 : X n), ∀ k : ℕ, m ≤ k →
      ∀ W ∈ nhds (0 : X m), ∃ U' ∈ nhds (0 : X k), ∃ r : ℝ, 0 < r ∧
        ∀ x ∈ U, ∀ y ∈ U', ((x : E) - (y : E)) ∈ V →
          ∃ w ∈ W, ((x : E) - (r : ℂ) • (w : E)) ∈ V) :
    IsBornological V := by sorry

end MasulloGRH
