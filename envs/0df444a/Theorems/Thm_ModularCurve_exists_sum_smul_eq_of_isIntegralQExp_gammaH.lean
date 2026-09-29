-- Prove2me | Theorems.Thm_ModularCurve_exists_sum_smul_eq_of_isIntegralQExp_gammaH
-- name    : ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gammaH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/bc743dc8-67e0-5d5c-9782-9a6813a3489f
-- title:
--   Forms with integral q-expansions span M_k(Γ_H(N))
-- statement:
--   Let $N$ be a non-zero natural number, let $H$ be a subgroup of $(\mathbb{Z}/N)^\times$, and let $k$ be an integer. Write $\Gamma_H(N)$ for the subgroup [`CohCarrier.GammaH N H`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}_2(\mathbb{Z})$, namely the image in $\mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H$ under the homomorphism $\Gamma_0(N) \to (\mathbb{Z}/N)^\times$ sending $\gamma$ to the unit with value the reduction modulo $N$ of its lower-right entry and inverse the reduction of its upper-left entry; it is viewed as a subgroup of $\mathrm{GL}_2(\mathbb{R})$. Let $F$ be a modular form of weight $k$ for this group. The assertion is that there exist a natural number $n$, scalars $c : \mathrm{Fin}\,n \to \mathbb{C}$, modular forms $G_i$ of weight $k$ for the same group $\Gamma_H(N)$, and integral power series $r_i \in \mathbb{Z}[[q]]$, such that for every $i$ the form $G_i$ satisfies [`ModularCurve.IsIntegralQExp (G i) (r i)`](def/ModularCurve_X1.html#L37), i.e. the image of $r_i$ under coefficientwise reduction along $\mathbb{Z} \to \mathbb{C}$ equals the $q$-expansion of $G_i$ of width $1$, and such that the underlying functions on the upper half-plane satisfy $F = \sum_i c_i\, G_i$.
--
--   This is the $\Gamma_H(N)$ form of the classical statement that $M_k(\Gamma, \mathbb{Z}) \otimes_{\mathbb{Z}} \mathbb{C} = M_k(\Gamma)$, i.e. that modular forms whose Fourier expansion at $\infty$ has integer coefficients span the full space over $\mathbb{C}$; it is deduced from the corresponding statement at level $\Gamma_1(N)$ together with the integrality of $q$-expansions of $\Gamma_0(N)$-translates. It is used downstream to reduce questions about $q$-expansion coefficients of forms on $\Gamma_H(N)$ and $\Gamma_0(N)$, and about Atkin–Lehner translates of cusp forms, to forms with integral coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_sum_smul_eq_of_isIntegralQExp_gammaH.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularCurve_X1
import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularFormClass
open scoped MatrixGroups ModularForm

theorem ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gammaH
    (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) {k : ℤ}
    (F : ModularForm (CohCarrier.GammaH N H) k) :
    ∃ (n : ℕ) (c : Fin n → ℂ)
      (G : Fin n → ModularForm (CohCarrier.GammaH N H) k)
      (r : Fin n → PowerSeries ℤ),
      (∀ i, ModularCurve.IsIntegralQExp (G i) (r i)) ∧
      (⇑F : UpperHalfPlane → ℂ) = ∑ i, c i • (⇑(G i) : UpperHalfPlane → ℂ) := by sorry
