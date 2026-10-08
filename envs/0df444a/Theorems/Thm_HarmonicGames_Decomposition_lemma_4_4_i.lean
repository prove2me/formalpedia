-- Prove2me | Theorems.Thm_HarmonicGames_Decomposition_lemma_4_4_i
-- name    : HarmonicGames.Decomposition.lemma_4_4_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:53:09.434059+00:00
-- url     : https://prove2.me/theorems/2ec4b48a-2f07-434d-8084-97d0243c8bc0
-- title:
--   Lemma 4.4 (i) — $D_m^\dagger = \frac{1}{h_m}D_m^*$
-- statement:
--   For a finite game with players $\mathcal M$ and nonempty finite strategy sets $E^m$ ($h_m = |E^m|$), let $D_m : C_0 \to C_1$ be the gradient along $m$-comparable profiles, $D : C_0^{\mathcal M}\to C_1$, $Du = \sum_m D_m u^m$, $\delta_0$ the gradient of the game graph, $\Pi = \operatorname{diag}(\Pi_1,\dots,\Pi_M)$ with $\Pi_m = D_m^\dagger D_m$. Adjoints ${}^*$ and Moore–Penrose pseudoinverses ${}^\dagger$ are taken for the inner products (7) on $C_0$, $C_1$ and the unweighted sum inner product $\langle u,v\rangle = \sum_m\langle u^m,v^m\rangle_0$ on $C_0^{\mathcal M}$.
--
--   **Lemma 4.4 (i).** For every player $m$,
--
--   $$
--   D_m^\dagger = \frac{1}{h_m}\,D_m^* .
--   $$
--
--   The pseudoinverse of each player's gradient is a rescaled adjoint (a divergence), so it can be computed without inverting anything. The identity depends on the factor $\tfrac12$ in the edge-flow inner product.
--
--
--   **Formalization Note** The five identities of Lemma 4.4 are split into five theorem items; this one is part (i). The paper's full statement is:
--
--   Lemma 4.4. The pseudoinverses of operators $D_m$ and $D$ satisfy the following identities: (i) $D_m^\dagger = \frac{1}{h_m}D_m^*$, (ii) $(\sum_i D_i)^\dagger D_j = (\sum_i D_i^*D_i)^\dagger D_j^*D_j$, (iii) $D^\dagger = [D_1^\dagger;\dots;D_M^\dagger]$, (iv) $\Pi = D^\dagger D$, (v) $DD^\dagger\delta_0 = \delta_0$.
-- source:
--   Candogan, Menache, Ozdaglar, Parrilo, Flows and Decompositions of Games: Harmonic and Potential Games, arXiv:1005.2405v2, p. 15, Lemma 4.4 (i)

import Mathlib
import Definitions.Def_HarmonicGames_Decomposition_Pinv
import Definitions.Def_HarmonicGames_Decomposition_Flows
import Definitions.Def_HarmonicGames_Decomposition_Games

namespace HarmonicGames.Decomposition

theorem lemma_4_4_i (ι : Type) [Fintype ι] [DecidableEq ι] (E : ι → Type) [∀ m, Fintype (E m)]
    [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)] (m : ι) :
    pinv (Dm E m) = (1 / (Fintype.card (E m) : ℝ)) • LinearMap.adjoint (Dm E m) := by sorry

end HarmonicGames.Decomposition
