-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_symplecticFourier_comp_rowAction_eq_inv_modulus_det_mul_symplecticFourier
-- name    : LanglandsTunnell.TateLocal.symplecticFourier_comp_rowAction_eq_inv_modulus_det_mul_symplecticFourier
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/17b66b5d-35dc-52ca-b8fb-a3d79ace6236
-- title:
--   Symplectic Fourier integral under right translation by GL₂
-- statement:
--   Let $p$ be a height-one prime of the ring of integers of $\mathbb{Q}$, and write $F = \mathbb{Q}_p$ for the completion $p.\text{adicCompletion}\ \mathbb{Q}$. Let $\Phi : F^2 \to \mathbb{C}$ be a function on row vectors indexed by `Fin 2` which is locally constant and has compact support, let $g \in \mathrm{GL}_2(F)$ with underlying matrix $(g_{ij})$ and determinant $d = \det g \in F^\times$, and let $w = (w_0, w_1) \in F^2$. Integration is against the product over `Fin 2` of `selfDualHaarAt`, the additive Haar measure on $F$ normalising the unit ball $\mathcal{O}_F$ to have mass $(\#(\mathcal{O}_{\mathbb{Q}}/p))^{-n/2}$, where $n$ is the level of the local character `psiLocal`, i.e. the supremum of the integers $m$ with $\psi(x) = 1$ whenever $v(x) \le \exp m$; here $\psi =$ `psiLocal` is the standard adelic additive character of $\mathbb{Q}$ restricted along the embedding of $F$ at $p$ into the adele ring, and the Borel $\sigma$-algebra is used on $F$. The assertion is the identity $$\int_{F^2} \Phi(u g)\, \psi(u_1 w_0 - u_0 w_1)\, du = \mathrm{modulus}(d)^{-1} \int_{F^2} \Phi(u)\, \psi(u_1 w'_0 - u_0 w'_1)\, du,$$ where $u g$ denotes the vector with $j$-th entry $u_0 g_{0j} + u_1 g_{1j}$, where $w'_0 = d^{-1}(w_0 g_{00} + w_1 g_{10})$ and $w'_1 = d^{-1}(w_0 g_{01} + w_1 g_{11})$, that is $w' = d^{-1}\, (w g)$, and where $\mathrm{modulus}(d)$ is the value at the unit $d$ of the distributive Haar character of $F$, viewed as a real, then complex, number.
--
--   This is the equivariance of the symplectic Fourier transform on $F^2$ under right translation by $\mathrm{GL}_2(F)$: translating the argument of $\Phi$ by $g$ rescales the transform by $|\det g|^{-1}$ and twists the spectral variable by $w \mapsto \det(g)^{-1} w g$, reflecting $\omega(ug, wg) = \det(g)\,\omega(u,w)$ for the symplectic form $\omega(u,w) = u_1 w_0 - u_0 w_1$. It is used in the local analysis of Godement–Whittaker type integrals, via [`LanglandsTunnell.CubicInduction.godementWhittaker2_symplecticFourier_swap_eq_godementWhittaker2_of_weight`](thm.html#LanglandsTunnell.CubicInduction.godementWhittaker2_symplecticFourier_swap_eq_godementWhittaker2_of_weight).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_symplecticFourier_comp_rowAction_eq_inv_modulus_det_mul_symplecticFourier.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open LanglandsTunnell.TateLocal

theorem LanglandsTunnell.TateLocal.symplecticFourier_comp_rowAction_eq_inv_modulus_det_mul_symplecticFourier
    (p : HeightOneSpectrum (𝓞 ℚ))
    (Φ : (Fin 2 → p.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (g : GL (Fin 2) (p.adicCompletion ℚ)) (w : Fin 2 → p.adicCompletion ℚ) :
    letI := localBorel ℚ p
    ∫ u : Fin 2 → p.adicCompletion ℚ, Φ (fun j : Fin 2 => u 0 * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 j + u 1 * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 j) *
        NumberField.StandardAddChar.psiLocal ℚ p (u 1 * w 0 - u 0 * w 1) ∂(Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p) =
      (((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ))⁻¹ *
        ∫ u : Fin 2 → p.adicCompletion ℚ, Φ u *
          NumberField.StandardAddChar.psiLocal ℚ p
            (u 1 * (((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)⁻¹ * (w 0 * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 0 + w 1 * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0)) -
             u 0 * (((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)⁻¹ * (w 0 * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1 + w 1 * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)))
          ∂(Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p) := by sorry
