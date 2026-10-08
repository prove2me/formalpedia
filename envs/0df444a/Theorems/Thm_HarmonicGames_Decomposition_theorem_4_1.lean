-- Prove2me | Theorems.Thm_HarmonicGames_Decomposition_theorem_4_1
-- name    : HarmonicGames.Decomposition.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:52:55.135255+00:00
-- url     : https://prove2.me/theorems/bccb4299-ff9d-4f55-9c30-ee63a0603b34
-- title:
--   Theorem 4.1 — every finite game decomposes uniquely as potential + harmonic + nonstrategic, $\mathcal G_{\mathcal M,E} = \mathcal P\oplus\mathcal H\oplus\mathcal N$
-- statement:
--   Consider finite games with a fixed finite set of players $\mathcal M$ and nonempty finite strategy sets $E^m$, identified with their utilities $u = (u^m)_m \in C_0^{\mathcal M} \cong \mathcal G_{\mathcal M,E}$. Let $D$ map a game to its flow of pairwise comparisons on the game graph, $\delta_0$ be the gradient of the game graph, $\Pi = \operatorname{diag}(\Pi_1,\dots,\Pi_M)$, and let $\mathcal P$, $\mathcal H$, $\mathcal N$ be the potential, harmonic and nonstrategic subspaces of Definition 4.2:
--
--   $$
--   \mathcal P = \{u \mid u = \Pi u,\ Du \in \operatorname{im}\delta_0\},\quad
--   \mathcal H = \{u \mid u = \Pi u,\ Du \in \ker\delta_0^*\},\quad
--   \mathcal N = \ker D .
--   $$
--
--   **Theorem 4.1.** The space of games is a direct sum of the potential, harmonic and nonstrategic subspaces,
--
--   $$
--   \mathcal G_{\mathcal M,E} = \mathcal P \oplus \mathcal H \oplus \mathcal N .
--   $$
--
--   In particular, every game $u$ decomposes uniquely into the three components
--
--   $$
--   u_P = D^\dagger\delta_0\delta_0^\dagger D u,\qquad
--   u_H = D^\dagger(I - \delta_0\delta_0^\dagger) D u,\qquad
--   u_N = (I - D^\dagger D) u,
--   $$
--
--   with $u_P + u_H + u_N = u$, $u_P \in \mathcal P$, $u_H \in \mathcal H$, $u_N \in \mathcal N$, and the potential function associated with $u_P$ is $\varphi = \delta_0^\dagger D u$.
--
--   This is the paper's main result: every finite game is, uniquely, a potential game plus a harmonic game plus a game without strategic content, and the components are given in closed form.
--
--   **Formalization Note** The statement has three parts: (1) every $u$ is $p + h + n$ for exactly one triple $(p,h,n) \in \mathcal P\times\mathcal H\times\mathcal N$ (the direct sum, stated independently of the formulas); (2) the formulas give components in $\mathcal P$, $\mathcal H$, $\mathcal N$ summing to $u$; (3) "$\varphi$ is the potential function of $u_P$" is stated as $Du_P = \delta_0\varphi$, which by (3)–(4) of the paper is Definition 2.1 (exact potential) for the game $u_P$. Pseudoinverses are for the $\tfrac12$-weighted inner product on edge flows and the unweighted sum inner product on $C_0^{\mathcal M}$; the subspaces themselves do not depend on these choices.
-- source:
--   Candogan, Menache, Ozdaglar, Parrilo, Flows and Decompositions of Games: Harmonic and Potential Games, arXiv:1005.2405v2, pp. 17–18, Theorem 4.1 (with Definition 4.2, eq. (28), p. 17)

import Mathlib
import Definitions.Def_HarmonicGames_Decomposition_Pinv
import Definitions.Def_HarmonicGames_Decomposition_Flows
import Definitions.Def_HarmonicGames_Decomposition_Games

namespace HarmonicGames.Decomposition

theorem theorem_4_1 (ι : Type) [Fintype ι] [DecidableEq ι] (E : ι → Type) [∀ m, Fintype (E m)]
    [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)] :
    (∀ u : Games E, ∃! t : potentialSubspace E × harmonicSubspace E × nonstrategicSubspace E,
        (t.1 : Games E) + (t.2.1 : Games E) + (t.2.2 : Games E) = u) ∧
    (∀ u : Games E,
        potentialComponent E u + harmonicComponent E u + nonstrategicComponent E u = u ∧
        potentialComponent E u ∈ potentialSubspace E ∧
        harmonicComponent E u ∈ harmonicSubspace E ∧
        nonstrategicComponent E u ∈ nonstrategicSubspace E) ∧
    (∀ u : Games E,
        Dop E (potentialComponent E u) = delta0 (gameGraph E) (potentialFunction E u)) := by sorry

end HarmonicGames.Decomposition
