-- Prove2me | Theorems.Thm_MasulloGRH_absolute_basis_shrinking_boundedly_complete
-- name    : MasulloGRH.absolute_basis_shrinking_boundedly_complete
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-21T04:39:34.154753+00:00
-- url     : https://prove2.me/theorems/58d57e2b-d81e-459e-8f35-0aa1627f9fd9
-- title:
--   Lemma 4.1.2.4 — absolute Schauder bases in complete barrelled reflexive spaces are shrinking and boundedly complete
-- statement:
--   Let $E$ be a Hausdorff locally convex space over $\mathbb C$. A sequence $(x_m)_{m\ge0}$ in $E$ with continuous linear functionals $(f_m)_{m\ge0}$ is a **Schauder basis** if $f_m(x_n)=\delta_{m,n}$ and $u=\sum_{m\ge0}f_m(u)x_m$ in $E$ for every $u\in E$. It is **equicontinuous** if the projections $P_k=\sum_{m\le k}f_m\cdot x_m$ form an equicontinuous sequence, and **absolute** if for every continuous seminorm $q$ there is a continuous seminorm $q'$ with $\sum_{m\ge0}q(f_m(u)x_m)\le q'(u)$ for all $u$.
--
--   Assume $E$ is complete, barrelled and reflexive, and let $(x_m)$ be an absolute Schauder basis with coefficient functionals $(f_m)$. Then:
--
--   1. $(x_m)$ is shrinking and boundedly complete.
--   2. $(f_m)$ is a Schauder basis of the strong dual $E'_\beta$, with coefficient functionals the evaluations at the $x_m$; it is unconditional and boundedly complete.
--   3. If $E$ is moreover nuclear, then $(f_m)$ is shrinking: the evaluations at the $x_m$ form a Schauder basis of the strong bidual $(E'_\beta)'_\beta$.
--
--   The lemma transfers a basis of $E$ to its strong dual, which the draft uses to expand distributions on spaces of $\theta$-functions.
--
--   **Formalization Note** In item 3 the evaluation at $x_m$ is the element of the bidual determined by $\varphi\mapsto\varphi(x_m)$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Chapter 4, §4.1.2, Lemma 4.1.2.4 (On absolute and unconditional Schauder bases), p. 159

import Definitions.Def_MasulloGRH_SchauderBases

set_option autoImplicit false

namespace MasulloGRH

theorem absolute_basis_shrinking_boundedly_complete
    (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : IsHLCS E) (hc : IsCompleteTVS E) (hb : BarrelledSpace ℂ E) (hr : IsReflexive E)
    (x : ℕ → E) (f : ℕ → StrongDual ℂ E) (hx : IsSchauderBasis x f) (habs : IsAbsoluteBasis x f) :
    IsShrinkingBasis x f ∧ IsBoundedlyCompleteBasis x ∧
    (IsDualSchauderBasis x f ∧
      (∀ φ : StrongDual ℂ E, Summable (fun m => φ (x m) • f m)) ∧
      IsBoundedlyCompleteBasis f) ∧
    (IsNuclear E → ∀ ψ : StrongDual ℂ (StrongDual ℂ E),
      Filter.Tendsto
        (fun k => ∑ m ∈ Finset.range (k + 1), ψ (f m) •
          (Classical.epsilon fun e : StrongDual ℂ (StrongDual ℂ E) =>
            ∀ φ : StrongDual ℂ E, e φ = φ (x m)))
        Filter.atTop (nhds ψ)) := by sorry

end MasulloGRH
