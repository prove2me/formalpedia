-- Prove2me | Theorems.Thm_MasulloGRH_schwartzBruhat_descent_goodSubgroup
-- name    : MasulloGRH.schwartzBruhat_descent_goodSubgroup
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T19:10:31.671366+00:00
-- url     : https://prove2.me/theorems/3f45119b-7a8a-4c07-9d10-a5b1a3e8e96d
-- title:
--   k-invariant Schwartz–Bruhat functions descend to G/k
-- statement:
--   Let $G$ be a second-countable, locally compact, Hausdorff abelian group and $k$ a good (hence compact) subgroup. If $f\in\mathcal S(G)$ is $k$-invariant, $f(gh)=f(g)$ for all $h\in k$, then $f$ descends to a Schwartz–Bruhat function on $G/k$:
--   $$\bar f(gk)=f(g),\qquad \bar f\in\mathcal S(G/k).$$
--   This identifies $\mathcal S(G)^k$ with a subspace of $\mathcal S(G/k)$ (§D.1.5). It is the step that makes the weight operators $T_a$ of the stages $\mathcal S_I(k,G)$ land in $\mathcal S(G/k)$.
--
--   Formalization note: $\bar f$ is written as $x\mapsto f(\bar x)$ using a chosen representative `x.out`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, §D.1.5 and §D.3.3

import Definitions.Def_MasulloGRH_SchwartzBruhat

set_option autoImplicit false

universe u

namespace MasulloGRH

theorem schwartzBruhat_descent_goodSubgroup
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (k : Subgroup G) (hk : IsGoodSubgroup k)
    (f : G → ℂ) (hf : f ∈ schwartzBruhatSubmodule G) (hinv : ∀ h ∈ k, ∀ g, f (g * h) = f g) :
    (fun x : G ⧸ k => f x.out) ∈ schwartzBruhatSubmodule (G ⧸ k) := by
  sorry

end MasulloGRH
