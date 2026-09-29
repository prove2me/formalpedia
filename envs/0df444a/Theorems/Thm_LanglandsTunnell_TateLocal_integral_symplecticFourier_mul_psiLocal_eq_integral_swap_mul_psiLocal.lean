-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_integral_symplecticFourier_mul_psiLocal_eq_integral_swap_mul_psiLocal
-- name    : LanglandsTunnell.TateLocal.integral_symplecticFourier_mul_psiLocal_eq_integral_swap_mul_psiLocal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/3812b5aa-034e-5f8e-b091-8c2a36260d97
-- title:
--   Partial Fourier transform of the symplectic Fourier transform swaps coordinates
-- statement:
--   Let $p$ be a height-one prime of the ring of integers of $\mathbb{Q}$, write $F = \mathbb{Q}_p$ for the completion `p.adicCompletion ℚ`, equipped with its Borel $\sigma$-algebra `localBorel`, let $\psi =$ `psiLocal ℚ p` be the local additive character obtained by composing the standard adelic character `stdAddChar` of $\mathbb{Q}$ with the additive embedding of $F$ into the adele ring at the place $p$, and let $dy =$ `selfDualHaarAt ℚ p` be the additive Haar measure normalised so that the local integers have mass $(\mathrm{N}p)^{-\mathrm{level}(\psi)/2}$, where the level is the supremum of the integers $n$ with $\psi$ trivial on $\{\mathrm{v}(x) \le q^{-n}\}$. Let $\Psi \colon F^2 \to \mathbb{C}$ be locally constant with compact support, and let $a, b \in F$. Then, with $du$ the product measure $dy\,dy$ on $F^2$ and with $\Psi^\sharp(v) = \int_{F^2} \Psi(u)\,\psi(u_1 v_0 - u_0 v_1)\,du$ the symplectic Fourier transform, one has $$\int_F \Psi^\sharp(a, y)\,\psi(b y)\,dy = \int_F \Psi(b, y)\,\psi(a y)\,dy,$$ pairs being written as the tuples $![a,y]$, $![b,y]$ in $F^2 = (\mathrm{Fin}\,2 \to F)$.
--
--   The identity says that taking the partial Fourier transform in the second variable converts the symplectic Fourier transform on $F^2$ into the interchange of the two arguments; it rests on Fourier inversion for the self-dual measure in Tate's local theory. It is used in the Langlands–Tunnell part of the development, in the proof that the Godement–Whittaker integral of weight type attached to a symplectically Fourier-transformed function agrees with the one attached to the coordinate swap.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_integral_symplecticFourier_mul_psiLocal_eq_integral_swap_mul_psiLocal.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open LanglandsTunnell.TateLocal

theorem LanglandsTunnell.TateLocal.integral_symplecticFourier_mul_psiLocal_eq_integral_swap_mul_psiLocal
    (p : HeightOneSpectrum (𝓞 ℚ))
    (Ψ : (Fin 2 → p.adicCompletion ℚ) → ℂ) (hΨ : IsLocallyConstant Ψ ∧ HasCompactSupport Ψ)
    (a b : p.adicCompletion ℚ) :
    letI := localBorel ℚ p
    ∫ y : p.adicCompletion ℚ,
        (fun v : Fin 2 → p.adicCompletion ℚ =>
            ∫ u : Fin 2 → p.adicCompletion ℚ, Ψ u * NumberField.StandardAddChar.psiLocal ℚ p (u 1 * v 0 - u 0 * v 1)
              ∂(Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p)) ![a, y] *
          NumberField.StandardAddChar.psiLocal ℚ p (b * y) ∂(selfDualHaarAt ℚ p) =
      ∫ y : p.adicCompletion ℚ, Ψ ![b, y] * NumberField.StandardAddChar.psiLocal ℚ p (a * y) ∂(selfDualHaarAt ℚ p) := by sorry
