-- Prove2me | Theorems.Thm_MasulloGRH_idele_class_group_topology
-- name    : MasulloGRH.idele_class_group_topology
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-21T03:36:10.50509+00:00
-- url     : https://prove2.me/theorems/93afcfe6-308c-4e2a-93a3-e42f2a30efa6
-- title:
--   Lemma A.1.3.4 — $F^\times$ is discrete in the ideles and $C_F$ is locally compact
-- statement:
--   Let $F$ be a number field, $\iota\colon F^\times\to\mathrm{GL}_1(\mathbb A_F)$ the diagonal embedding and $C_F=\mathrm{GL}_1(\mathbb A_F)/F^\times$ the idele class group.
--
--   1. $\iota$ is a closed map when $F^\times$ carries the discrete topology, and its image is discrete.
--   2. $C_F$ is Hausdorff and locally compact.
--   3. The idelic norm is trivial on $F^\times$ (the product formula), so it descends to $C_F$, and it is surjective onto $\mathbb R_{>0}$.
--   4. The norm $|\cdot|_F\colon C_F\to\mathbb R_{>0}$ has a continuous homomorphic section: there is a continuous homomorphism $\sigma\colon\mathbb R_{>0}\to C_F$ with $|\sigma(t)|_F=t$ for all $t>0$.
--
--   The section splits $C_F$ as $\mathbb R_{>0}\times C_F^1$, which is how quasi-characters of $C_F$ are parametrized as $\chi|\cdot|_F^s$.
--
--   **Formalization Note** The section is a function on $\mathbb R$ of which only the values on $(0,\infty)$ are used. The condition $|\sigma(t)|_F=t$ is stated as: the class $\sigma(t)$ has a representative idele of norm $t$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix A, §A.1.3.2, Lemma A.1.3.4, eqs. (A.1.3.5)–(A.1.3.6), p. 542

import Definitions.Def_MasulloGRH_IdeleNorm

set_option autoImplicit false

namespace MasulloGRH

open NumberField IsDedekindDomain

theorem idele_class_group_topology (F : Type*) [Field F] [NumberField F] :
    (∀ A : Set Fˣ, IsClosed (principalIdele F '' A)) ∧
    DiscreteTopology (principalIdeles F) ∧
    T2Space (IdeleClassGroup F) ∧ LocallyCompactSpace (IdeleClassGroup F) ∧
    (∀ ξ : Fˣ, ideleNorm (principalIdele F ξ) = 1) ∧
    (∀ t : ℝ, 0 < t → ∃ g : IdeleGroup F, ideleNorm g = t) ∧
    ∃ σ : ℝ → IdeleClassGroup F, ContinuousOn σ (Set.Ioi 0) ∧
      (∀ t u : ℝ, 0 < t → 0 < u → σ (t * u) = σ t * σ u) ∧
      ∀ t : ℝ, 0 < t → ∃ g : IdeleGroup F, QuotientGroup.mk g = σ t ∧ ideleNorm g = t := by sorry

end MasulloGRH
