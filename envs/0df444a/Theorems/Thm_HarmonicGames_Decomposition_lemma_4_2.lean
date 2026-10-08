-- Prove2me | Theorems.Thm_HarmonicGames_Decomposition_lemma_4_2
-- name    : HarmonicGames.Decomposition.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:52:59.340056+00:00
-- url     : https://prove2.me/theorems/d3ad308a-1407-429b-92f5-3e671b6e68a7
-- title:
--   Lemma 4.2 — $\ker D_m = \ker\Pi_m = \ker\Delta_{0,m}$, with basis $\{\nu_{q^{-m}}\}$
-- statement:
--   For a finite game with nonempty finite strategy sets, let $D_m$, $\Pi_m = D_m^\dagger D_m$ and $\Delta_{0,m} = D_m^*D_m$ be as in Section 4.1, and for each profile $q^{-m} \in E^{-m}$ of the players other than $m$ let $\nu_{q^{-m}} \in C_0$ be
--
--   $$
--   \nu_{q^{-m}}(p) = \begin{cases} 1 & \text{if } p^{-m} = q^{-m},\\ 0 & \text{otherwise.}\end{cases}
--   $$
--
--   **Lemma 4.2.** The kernels of $D_m$, $\Pi_m$ and $\Delta_{0,m}$ coincide, $\ker(D_m) = \ker(\Pi_m) = \ker(\Delta_{0,m})$, and the collection $\{\nu_{q^{-m}}\}_{q^{-m} \in E^{-m}}$ is a basis of these kernels.
--
--   The kernel of $D_m$ consists of the utilities of player $m$ that do not depend on $m$'s own strategy — the nonstrategic information. The basis gives $\dim\ker D_m = |E^{-m}|$.
--
--   **Formalization Note** "Basis" is stated as linear independence of the family $\nu$ together with its span being $\ker D_m$. The index $q^{-m}$ ranges over functions on the players $k \ne m$, and $p^{-m} = q^{-m}$ means $p_k = q_k$ for all $k \ne m$.
-- source:
--   Candogan, Menache, Ozdaglar, Parrilo, Flows and Decompositions of Games: Harmonic and Potential Games, arXiv:1005.2405v2, p. 15, Lemma 4.2, eq. (26)

import Mathlib
import Definitions.Def_HarmonicGames_Decomposition_Pinv
import Definitions.Def_HarmonicGames_Decomposition_Flows
import Definitions.Def_HarmonicGames_Decomposition_Games

namespace HarmonicGames.Decomposition

theorem lemma_4_2 (ι : Type) [Fintype ι] [DecidableEq ι] (E : ι → Type) [∀ m, Fintype (E m)]
    [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)] (m : ι) :
    LinearMap.ker (Dm E m) = LinearMap.ker (Pim E m) ∧
    LinearMap.ker (Pim E m) = LinearMap.ker (Delta0m E m) ∧
    LinearIndependent ℝ (nu E m) ∧
    Submodule.span ℝ (Set.range (nu E m)) = LinearMap.ker (Dm E m) := by sorry

end HarmonicGames.Decomposition
