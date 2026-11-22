-- Prove2me | Theorems.Thm_MasulloGRH_expDecaySchwartz_exists_stages
-- name    : MasulloGRH.expDecaySchwartz_exists_stages
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T17:54:57.445314+00:00
-- url     : https://prove2.me/theorems/f3efcc9c-acf5-497a-aeff-51aad3c2c34e
-- title:
--   Retract stages for $\mathcal S_I(G)$
-- statement:
--   Let $(G,|\cdot|_G)$ be a second countable Hausdorff locally compact abelian group with a surjective module $|\cdot|_G\colon G\to\mathbb R_{>0}$, and let $I\subset\mathbb R$ be a non-empty interval. Let $\mathcal S_I(G)$ be the space of continuous $\phi$ on $G$ with $|\cdot|_G^a\phi\in\mathcal S(G)$ for all $a\in I$, with its inductive topology (Definition D.3.3.3).
--
--   Then there are nuclear Fréchet spaces $F_N$ ($N\ge0$) and continuous linear maps
--   $$J_N\colon F_N\to\mathcal S_I(G),\qquad P_N\colon\mathcal S_I(G)\to F_N$$
--   with the following properties:
--   - $P_N J_N=\mathrm{id}_{F_N}$;
--   - the images $J_N(F_N)$ increase and exhaust $\mathcal S_I(G)$;
--   - the topology of $\mathcal S_I(G)$ is the finest locally convex topology making every $J_N$ continuous.
--
--   In the draft, the stages are the spaces $\mathcal S_I(k_N,G)$ of $k_N$-invariant elements for a suitable sequence of good compact subgroups $k_N$. Each carries the projective topology of countably many weights $T_{a_j}$, $a_j\in I$, into the nuclear Fréchet spaces $\mathcal S(G/k_N)$. The maps $P_N$ are averaging over $k_N$. Together with the proved abstract lemma `isStrictLFOfNuclearFrechet_of_retract_stages`, this gives that $\mathcal S_I(G)$ is a strict LF-space of nuclear Fréchet spaces.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, Definitions D.3.3.1–D.3.3.3 and proof of Theorem D.3.3.7 (pp. 804–807); cf. the analogous schwartzBruhat_exists_stages for Theorem D.1.5.7

import Definitions.Def_MasulloGRH_ExpDecaySpaces

set_option autoImplicit false

universe u

namespace MasulloGRH

theorem expDecaySchwartz_exists_stages
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (m : G → ℝ) (hm : IsRposModule m)
    (I : Set ℝ) (hI : I.OrdConnected) (hne : I.Nonempty) :
    ∃ (F : ℕ → Type u) (_ : ∀ N, AddCommGroup (F N)) (_ : ∀ N, Module ℂ (F N))
      (_ : ∀ N, TopologicalSpace (F N))
      (J : (N : ℕ) → F N →ₗ[ℂ] ExpDecaySchwartz G m I)
      (P : (N : ℕ) → ExpDecaySchwartz G m I →ₗ[ℂ] F N),
      (∀ N, IsFrechet (F N) ∧ IsNuclear (F N)) ∧
      (∀ N, Continuous (J N)) ∧ (∀ N, Continuous (P N)) ∧
      (∀ N y, P N (J N y) = y) ∧
      (∀ N M, N ≤ M → LinearMap.range (J N) ≤ LinearMap.range (J M)) ∧
      (∀ x : ExpDecaySchwartz G m I, ∃ N, x ∈ LinearMap.range (J N)) ∧
      (inferInstance : TopologicalSpace (ExpDecaySchwartz G m I)) =
        sInf {t | IsLocallyConvexTopology (ExpDecaySchwartz G m I) t ∧
          ∀ N, @Continuous (F N) (ExpDecaySchwartz G m I) _ t (J N)} := by
  sorry

end MasulloGRH
