-- Prove2me | Theorems.Thm_MasulloGRH_strictLF_quotient_weakQ_of_alpha_regular
-- name    : MasulloGRH.strictLF_quotient_weakQ_of_alpha_regular
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-20T23:58:46.474283+00:00
-- url     : https://prove2.me/theorems/934d987d-0e3c-4331-a464-b03af37ca5f1
-- title:
--   Weak condition (wQ) from α-regularity of a Fréchet quotient spectrum
-- statement:
--   Let $E$ be the strict countable locally convex inductive limit of increasing Fréchet subspaces $E_n$, and let $V$ be closed in $E$. Write $q:E\to E/V$ for the quotient map and $P_n=E_n/(E_n\cap V)$. Identify $P_n$ with its image as a vector subspace of $E/V$, keeping the quotient topology of $E_n$ on $P_n$.
--
--   Assume the quotient is $\alpha$-regular, meaning that every bounded subset of $E/V$ lies in some $P_n$. Then the spectrum $(P_n)$ satisfies $(wQ)$.
--
--   Vogt’s condition $(wQ)$ for the quotient spectrum means that for each $n$ there are $m\ge n$ and a zero-neighborhood $U\subset E_n$ such that, for each $k\ge m$ and each zero-neighborhood $W\subset E_m$, there are a zero-neighborhood $U'\subset E_k$ and a number $r>0$ satisfying
--   $$
--   q(U)\cap q(U')\subseteq r\,q(W).
--   $$
--   The stage quotient maps are open, so choosing zero-neighborhoods before passing to the quotients gives the same condition.
-- source:
--   J. Wengenroth, Acyclic inductive spectra of Fréchet spaces, Studia Mathematica 120 (1996), 247–258, https://matwbn.icm.edu.pl/ksiazki/sm/sm120/sm12035.pdf; Definition 3.1 and Proposition 3.2, pp. 252–253

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem strictLF_quotient_weakQ_of_alpha_regular
    (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hα : ∀ B : Set (E ⧸ V), Bornology.IsVonNBounded ℂ B →
      ∃ n : ℕ, B ⊆ Set.range (Submodule.mapQ (V.comap (X n).subtype) V (X n).subtype le_rfl)) :
    ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ∃ U ∈ nhds (0 : X n), ∀ k : ℕ, m ≤ k →
      ∀ W ∈ nhds (0 : X m), ∃ U' ∈ nhds (0 : X k), ∃ r : ℝ, 0 < r ∧
        ∀ x ∈ U, ∀ y ∈ U', ((x : E) - (y : E)) ∈ V →
          ∃ w ∈ W, ((x : E) - (r : ℂ) • (w : E)) ∈ V := by sorry

end MasulloGRH
