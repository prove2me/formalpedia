-- Prove2me | Theorems.Thm_HarmonicGames_Decomposition_lemma_4_4_ii
-- name    : HarmonicGames.Decomposition.lemma_4_4_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:52:51.790743+00:00
-- url     : https://prove2.me/theorems/ab752838-790d-4a2d-8a63-06fb364574c8
-- title:
--   Lemma 4.4 (ii) — $(\sum_i D_i)^\dagger D_j = (\sum_i D_i^*D_i)^\dagger D_j^*D_j$
-- statement:
--   For a finite game with players $\mathcal M$ and nonempty finite strategy sets $E^m$ ($h_m = |E^m|$), let $D_m : C_0 \to C_1$ be the gradient along $m$-comparable profiles, $D : C_0^{\mathcal M}\to C_1$, $Du = \sum_m D_m u^m$, $\delta_0$ the gradient of the game graph, $\Pi = \operatorname{diag}(\Pi_1,\dots,\Pi_M)$ with $\Pi_m = D_m^\dagger D_m$. Adjoints ${}^*$ and Moore–Penrose pseudoinverses ${}^\dagger$ are taken for the inner products (7) on $C_0$, $C_1$ and the unweighted sum inner product $\langle u,v\rangle = \sum_m\langle u^m,v^m\rangle_0$ on $C_0^{\mathcal M}$.
--
--   **Lemma 4.4 (ii).** For every player $j$,
--
--   $$
--   \Big(\sum_i D_i\Big)^\dagger D_j = \Big(\sum_i D_i^* D_i\Big)^\dagger D_j^* D_j .
--   $$
--
--   Since $\sum_i D_i = \delta_0$ and $\sum_i D_i^*D_i = \Delta_0$, this rewrites the potential function of Theorem 4.1 as $\varphi = \Delta_0^\dagger\sum_m \Delta_{0,m}u^m$, which involves only operators on $C_0$.
--
--
--   **Formalization Note** The five identities of Lemma 4.4 are split into five theorem items; this one is part (ii). The paper's full statement is:
--
--   Lemma 4.4. The pseudoinverses of operators $D_m$ and $D$ satisfy the following identities: (i) $D_m^\dagger = \frac{1}{h_m}D_m^*$, (ii) $(\sum_i D_i)^\dagger D_j = (\sum_i D_i^*D_i)^\dagger D_j^*D_j$, (iii) $D^\dagger = [D_1^\dagger;\dots;D_M^\dagger]$, (iv) $\Pi = D^\dagger D$, (v) $DD^\dagger\delta_0 = \delta_0$.
--
--   The left-hand side is stated with the sum $\sum_i D_i$, as printed (not with $\delta_0$).
-- source:
--   Candogan, Menache, Ozdaglar, Parrilo, Flows and Decompositions of Games: Harmonic and Potential Games, arXiv:1005.2405v2, p. 15, Lemma 4.4 (ii)

import Mathlib
import Definitions.Def_HarmonicGames_Decomposition_Pinv
import Definitions.Def_HarmonicGames_Decomposition_Flows
import Definitions.Def_HarmonicGames_Decomposition_Games

namespace HarmonicGames.Decomposition

theorem lemma_4_4_ii (ι : Type) [Fintype ι] [DecidableEq ι] (E : ι → Type) [∀ m, Fintype (E m)]
    [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)] (j : ι) :
    pinv (∑ i, Dm E i) ∘ₗ Dm E j =
      pinv (∑ i, LinearMap.adjoint (Dm E i) ∘ₗ Dm E i) ∘ₗ
        (LinearMap.adjoint (Dm E j) ∘ₗ Dm E j) := by sorry

end HarmonicGames.Decomposition
