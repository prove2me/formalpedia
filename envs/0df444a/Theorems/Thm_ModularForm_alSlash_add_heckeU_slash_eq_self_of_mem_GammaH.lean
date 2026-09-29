-- Prove2me | Theorems.Thm_ModularForm_alSlash_add_heckeU_slash_eq_self_of_mem_GammaH
-- name    : ModularForm.alSlash_add_heckeU_slash_eq_self_of_mem_GammaH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/804f91f2-3bdf-571d-861a-10013c3c318b
-- title:
--   Invariance of f∣ W + Uₚ f at level R
-- statement:
--   Let $M$ be a nonzero natural number, $p$ a prime, and let $W$ be an Atkin–Lehner datum for the pair $(M,p)$: a natural number $R=W.R$ with $M = pR$ together with integers $a,b$ satisfying $pa - Rb = 1$. Let $H$ be a subgroup of $(\mathbb{Z}/M\mathbb{Z})^\times$ containing every unit that reduces to $1$ under the reduction map $(\mathbb{Z}/M\mathbb{Z})^\times \to (\mathbb{Z}/R\mathbb{Z})^\times$ coming from $R \mid M$. Let $f : \mathfrak{H} \to \mathbb{C}$ be a function invariant for the weight-two slash action under the image in $\mathrm{GL}_2(\mathbb{R})$ of $\Gamma_H(M)$, the subgroup of $\Gamma_0(M)$ consisting of those $\gamma$ whose lower-right entry, read as a unit of $\mathbb{Z}/M\mathbb{Z}$, lies in $H$. Let $g \in \mathrm{SL}_2(\mathbb{Z})$ lie in $\Gamma_0(R)$ and suppose its lower-right entry, as a unit of $\mathbb{Z}/R\mathbb{Z}$, is the reduction modulo $R$ of some element of $H$. Then the function $f \mid_2 W.\mathrm{alGL} + \sum_{j=0}^{p-1} f \mid_2 \begin{pmatrix} 1 & j \\ 0 & p\end{pmatrix}$, where $W.\mathrm{alGL}$ is the integral Atkin–Lehner matrix of the datum viewed in $\mathrm{GL}_2(\mathbb{R})$, is unchanged by the weight-two slash action of $g$.
--
--   This is the classical statement that, for $p$ exactly dividing $M$, the trace $f\mid_2 W_p + U_p f$ of a weight-two form of level $\Gamma_H(M)$ descends to level $\Gamma_{H'}(R)$ with $R = M/p$ and $H'$ the image of $H$, here in the form of invariance under one group element at a time. It is used in the level-lowering step, in the computation of $q$-expansion coefficients of $f\mid_2 W_p$ and in the analysis of the two-dimensional cuspidal eigenspaces attached to $U_p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_alSlash_add_heckeU_slash_eq_self_of_mem_GammaH.lean

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularForm_AtkinLehnerDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularForm.alSlash_add_heckeU_slash_eq_self_of_mem_GammaH
    {M p : ℕ} [NeZero M] (hp : p.Prime) (W : ModularForm.AtkinLehnerDatum M p)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H)
    {f : UpperHalfPlane → ℂ}
    (hf : ∀ γ ∈ (CohCarrier.GammaH M H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)),
      SlashAction.map (2 : ℤ) γ f = f)
    (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hg : g ∈ CongruenceSubgroup.Gamma0 W.R)
    (hgH : ∃ u ∈ H,
      ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = CohCarrier.gamma0Units W.R ⟨g, hg⟩) :
    SlashAction.map (2 : ℤ) (Matrix.SpecialLinearGroup.mapGL ℝ g)
        (ModularForm.alSlash W 2 f + ModularForm.heckeU 2 p f) =
      ModularForm.alSlash W 2 f + ModularForm.heckeU 2 p f := by sorry
