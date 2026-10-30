-- Prove2me | Theorems.Thm_JuschenkoMonod_exists_orbitIndexing_monoidHom_unique_and_injective_of_dense
-- name    : JuschenkoMonod.exists_orbitIndexing_monoidHom_unique_and_injective_of_dense
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T17:28:44.506983+00:00
-- url     : https://prove2.me/theorems/44984636-a8d1-4363-9e53-7199f8df1eca
-- title:
--   p. 786 — π_p, defined by g(T^j p) = T^{π_p(g)(j)} p, is a homomorphism [[T]] → W(ℤ), injective when the orbit of p is dense
-- statement:
--   Let $T$ be a homeomorphism of a Cantor space $C$ with no finite orbits (every orbit $\{T^kx : k \in \mathbf Z\}$ is infinite), and let $p \in C$. Then there is a group homomorphism $\pi_p\colon [[T]] \to W(\mathbf Z)$ such that
--   - $g(T^jp) = T^{\pi_p(g)(j)}p$ for every $g \in [[T]]$ and $j \in \mathbf Z$;
--   - every map $\psi$ from $[[T]]$ to the permutations of $\mathbf Z$ with $g(T^jp) = T^{\psi(g)(j)}p$ for all $g$ and $j$ equals $\pi_p$;
--   - if the orbit $\{T^kp : k \in \mathbf Z\}$ is dense in $C$, then $\pi_p$ is injective.
--
--   *Formalization note.* "we can define a map $\pi_p\colon [[T]] \longrightarrow W(\mathbf Z)$ by the requirement" is stated as: a homomorphism into $W(\mathbf Z)$ satisfying the requirement exists, and the requirement determines it among all maps into the permutations of $\mathbf Z$.
-- source:
--   Juschenko, K. and Monod, N., Cantor systems, piecewise translations and simple amenable groups, Ann. of Math. (2) 178 (2013) 775–787, https://doi.org/10.4007/annals.2013.178.2.7, p. 786, the homomorphism π_p

import Mathlib
import Definitions.Def_IntervalExchange
import Definitions.Def_CantorSystems
import Definitions.Def_JuschenkoMonod

namespace JuschenkoMonod

theorem exists_orbitIndexing_monoidHom_unique_and_injective_of_dense (C : Type*) [TopologicalSpace C]
    (hC : CantorSystems.IsCantorSpace C) (T : C ≃ₜ C)
    (hT : ∀ x : C, (Set.range fun k : ℤ => (T ^ k) x).Infinite) (p : C) :
    ∃ φ : fullGroup T →* IntervalExchange.wobbling ℤ,
      IsOrbitIndexing T p (fun g => (φ g : Equiv.Perm ℤ)) ∧
      (∀ ψ : fullGroup T → Equiv.Perm ℤ, IsOrbitIndexing T p ψ → ψ = fun g => (φ g : Equiv.Perm ℤ)) ∧
      (Dense (Set.range fun k : ℤ => (T ^ k) p) → Function.Injective φ) := by
  sorry

end JuschenkoMonod
