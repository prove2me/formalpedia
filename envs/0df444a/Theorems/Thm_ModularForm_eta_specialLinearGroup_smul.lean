-- Prove2me | Theorems.Thm_ModularForm_eta_specialLinearGroup_smul
-- name    : ModularForm.eta_specialLinearGroup_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/9d9dea3c-c33f-5f83-801b-957a1764983c
-- title:
--   Dedekind's η transformation law for c>0
-- statement:
--   Let $\gamma$ be an element of $\mathrm{SL}_2(\mathbb{Z})$, written entrywise as the matrix with entries $a=\gamma_{00}$, $b=\gamma_{01}$, $c=\gamma_{10}$, $d=\gamma_{11}$, and assume $c>0$; let $z$ lie in the upper half-plane. The assertion is an equality of complex numbers: the Dedekind eta function `ModularForm.eta`, evaluated at the complex number underlying the Möbius action $\gamma\cdot z$, equals
--   $$\exp\!\Big(\frac{\pi i}{12}\,\Phi\Big)\cdot \mathrm{sqrt}\big(-i\,(cz+d)\big)\cdot \eta(z),$$
--   where $\Phi$ is the rational number $(a+d)/c - 12\,s(d,c)$, formed using the natural number `c.toNat` as denominator and second argument and then coerced into $\mathbb{C}$, and $\mathrm{sqrt}$ is Mathlib's principal complex square root (the argument $-i(cz+d)$ has positive real part $c\,\mathrm{Im}\,z$, so the branch is unambiguous). Here $s(h,k)=\sum_{r=0}^{k-1}((r/k))\,((hr/k))$ with $((x))$ the sawtooth $\mathrm{frac}(x)-1/2$, set to $0$ when $\mathrm{frac}(x)=0$; no coprimality of $d$ and $c$ is assumed in this definition, although $\gcd(d,c)=1$ holds automatically.
--
--   This is Dedekind's transformation law for $\eta$ in Rademacher's normalisation, with the multiplier written through the function $\Phi(\gamma)=(a+d)/c-12\,s(d,c)$ and the automorphy factor as $\sqrt{-i(cz+d)}$. It is used in the construction of [`ModularCurve.sharpUnitInvariant`](thm.html#ModularCurve.sharpUnitInvariant), and the cited inputs are the $S$-transformation and translation laws for $\eta$, a product rule for the principal square root on the right half-plane, and the cocycle-type step identity [`rademacher_phi_step`](thm.html#rademacher_phi_step) for $\Phi$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_eta_specialLinearGroup_smul.lean

import Definitions.Def_NumberTheory_DedekindSum
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularForm.eta_specialLinearGroup_smul (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hc : 0 < (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) (z : UpperHalfPlane) : ModularForm.eta ((γ • z : UpperHalfPlane) : ℂ) = Complex.exp (Real.pi * Complex.I / 12 * (((((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ℚ) / ((((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0).toNat : ℕ) : ℚ) - 12 * dedekindSum ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0).toNat : ℚ) : ℂ)) * Complex.sqrt (-Complex.I * (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * (z : ℂ) + ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ))) * ModularForm.eta z := by sorry
