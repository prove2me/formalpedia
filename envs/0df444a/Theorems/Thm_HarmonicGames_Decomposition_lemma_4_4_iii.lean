-- Prove2me | Theorems.Thm_HarmonicGames_Decomposition_lemma_4_4_iii
-- name    : HarmonicGames.Decomposition.lemma_4_4_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:52:53.916978+00:00
-- url     : https://prove2.me/theorems/0ecad2a7-5794-4d57-ac54-813d0998d710
-- title:
--   Lemma 4.4 (iii) — $D^\dagger = [D_1^\dagger;\dots;D_M^\dagger]$
-- statement:
--   For a finite game with players $\mathcal M$ and nonempty finite strategy sets $E^m$ ($h_m = |E^m|$), let $D_m : C_0 \to C_1$ be the gradient along $m$-comparable profiles, $D : C_0^{\mathcal M}\to C_1$, $Du = \sum_m D_m u^m$, $\delta_0$ the gradient of the game graph, $\Pi = \operatorname{diag}(\Pi_1,\dots,\Pi_M)$ with $\Pi_m = D_m^\dagger D_m$. Adjoints ${}^*$ and Moore–Penrose pseudoinverses ${}^\dagger$ are taken for the inner products (7) on $C_0$, $C_1$ and the unweighted sum inner product $\langle u,v\rangle = \sum_m\langle u^m,v^m\rangle_0$ on $C_0^{\mathcal M}$.
--
--   **Lemma 4.4 (iii).** The pseudoinverse of $D$ is the stacked operator
--
--   $$
--   D^\dagger = [D_1^\dagger; \dots; D_M^\dagger],\qquad\text{i.e.}\qquad (D^\dagger X)^m = D_m^\dagger X \quad\text{for all } X \in C_1,\ m \in \mathcal M .
--   $$
--
--   It reduces the pseudoinverse of the whole game-to-flow map to the players' individual pseudoinverses.
--
--
--   **Formalization Note** The five identities of Lemma 4.4 are split into five theorem items; this one is part (iii). The paper's full statement is:
--
--   Lemma 4.4. The pseudoinverses of operators $D_m$ and $D$ satisfy the following identities: (i) $D_m^\dagger = \frac{1}{h_m}D_m^*$, (ii) $(\sum_i D_i)^\dagger D_j = (\sum_i D_i^*D_i)^\dagger D_j^*D_j$, (iii) $D^\dagger = [D_1^\dagger;\dots;D_M^\dagger]$, (iv) $\Pi = D^\dagger D$, (v) $DD^\dagger\delta_0 = \delta_0$.
-- source:
--   Candogan, Menache, Ozdaglar, Parrilo, Flows and Decompositions of Games: Harmonic and Potential Games, arXiv:1005.2405v2, p. 15, Lemma 4.4 (iii)

import Mathlib
import Definitions.Def_HarmonicGames_Decomposition_Pinv
import Definitions.Def_HarmonicGames_Decomposition_Flows
import Definitions.Def_HarmonicGames_Decomposition_Games

namespace HarmonicGames.Decomposition

theorem lemma_4_4_iii (ι : Type) [Fintype ι] [DecidableEq ι] (E : ι → Type) [∀ m, Fintype (E m)]
    [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)] (X : Flow E) (m : ι) :
    pinv (Dop E) X m = pinv (Dm E m) X := by sorry

end HarmonicGames.Decomposition
