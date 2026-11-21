-- Prove2me | Theorems.Thm_MasulloGRH_idele_group_topology
-- name    : MasulloGRH.idele_group_topology
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-21T03:35:38.184183+00:00
-- url     : https://prove2.me/theorems/cb41afeb-c3b5-4448-99ae-2c7b7c4a188f
-- title:
--   Lemma A.1.3.3 — the idele group is locally compact and the idelic norm is continuous
-- statement:
--   Let $F$ be a number field and $\mathrm{GL}_1(\mathbb A_F)$ its idele group, i.e. the units of the adele ring with the topology induced by $x\mapsto(x,x^{-1})$.
--
--   1. $\mathrm{GL}_1(\mathbb A_F)$ is Hausdorff and locally compact.
--   2. The idele group is the restricted product of the groups $F_v^\times$ with respect to the unit groups $\mathcal O_{F_v}^\times$ as a topological group: the canonical bijection between the units of the finite adele ring and the restricted product $\widehat{\prod}_{v\in\Sigma_{F,f}}(F_v^\times,\mathcal O_{F_v}^\times)$ is a homeomorphism.
--   3. The idelic norm $|g|_F=\prod_v|g_v|_v$ is a continuous homomorphism $\mathrm{GL}_1(\mathbb A_F)\to\mathbb R_{>0}$.
--   4. The subgroup $\mathrm{GL}_1(\mathbb A_F)^1$ of ideles of norm $1$ is closed.
--
--   These are the basic topological facts about the ideles used in every later construction on $C_F$.
--
--   **Formalization Note** The adele ring is the product of the infinite adele ring and the finite adele ring, so the idele group is the product of the finitely many groups $F_v^\times$, $v\mid\infty$, and the units of the finite adele ring; item 2 is stated for the finite part.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix A, §A.1.3.1, Lemma A.1.3.3, pp. 541–542

import Definitions.Def_MasulloGRH_IdeleNorm

set_option autoImplicit false

namespace MasulloGRH

open NumberField IsDedekindDomain

theorem idele_group_topology (F : Type*) [Field F] [NumberField F] :
    T2Space (IdeleGroup F) ∧ LocallyCompactSpace (IdeleGroup F) ∧
    (Continuous
        (RestrictedProduct.unitsEquiv (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) :
          (FiniteAdeleRing (𝓞 F) F)ˣ ≃* _) ∧
      Continuous
        (RestrictedProduct.unitsEquiv (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) :
          (FiniteAdeleRing (𝓞 F) F)ˣ ≃* _).symm) ∧
    Continuous (ideleNorm : IdeleGroup F → ℝ) ∧
    (∀ g h : IdeleGroup F, ideleNorm (g * h) = ideleNorm g * ideleNorm h) ∧
    (∀ g : IdeleGroup F, 0 < ideleNorm g) ∧
    IsClosed {g : IdeleGroup F | ideleNorm g = 1} := by sorry

end MasulloGRH
