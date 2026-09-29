-- Prove2me | Theorems.Thm_HolographicQuantumMatter_radial_solutions_zero_momentum
-- name    : HolographicQuantumMatter.radial_solutions_zero_momentum
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-27T18:56:56.102985+00:00
-- url     : https://prove2.me/theorems/f9998ed1-8380-417d-9827-b593947e4a3f
-- title:
--   Two integration constants: $\phi=A\,r^{\Delta_-}+B\,r^{\Delta_+}$ (eq. 28, $\omega=k=0$)
-- statement:
--   Let $d\ge0$, $L>0$ and $m^2\in\mathbb R$ with $m^2L^2>-\frac{(d+1)^2}{4}$ (strictly above the Breitenlohner–Freedman bound), and let $\Delta_\pm=\frac{d+1}{2}\pm\sqrt{\frac{(d+1)^2}{4}+m^2L^2}$. A function $\phi$ is a $C^2$ solution on $r>0$ of the zero-frequency, zero-momentum radial equation
--
--   $$\phi''-\frac{d}{r}\phi'-\frac{m^2L^2}{r^2}\phi=0$$
--
--   if and only if there are constants $A,B\in\mathbb R$ with
--
--   $$\phi(r)=A\,r^{\Delta_-}+B\,r^{\Delta_+}\qquad\text{for all } r>0 .$$
--
--   This is the expansion (28) in the case $\omega=k=0$, where it is exact: the two constants of integration are the source $\phi_{(0)}\propto A$ (multiplying $r^{d+1-\Delta_+}=r^{\Delta_-}$) and the response $\phi_{(1)}\propto B$.
--
--   **Formalization Note** The boundary theory has $d$ spatial dimensions (so the bulk is $\mathrm{AdS}_{d+2}$), following the source's convention. The bulk mass squared is a real parameter $m^2$ (called `msq`), allowed to be negative; the source writes $(mL)^2$ for $m^2L^2$. Fields are real-valued functions of $r$; only their values on $r>0$ matter. The strict inequality excludes the BF-saturating case $\Delta_+=\Delta_-$, where a logarithmic solution appears.
-- source:
--   Hartnoll, Lucas, Sachdev, *Holographic quantum matter*, arXiv:1612.07324v3, https://arxiv.org/abs/1612.07324, Section 1.6.2, p. 10, eqs. (27)–(29) (with $d+1-\Delta_\pm=\Delta_\mp$)

import Mathlib
import Definitions.Def_HolographicQuantumMatter_ScalarAdS

namespace HolographicQuantumMatter

theorem radial_solutions_zero_momentum (d : ℕ) (msq L : ℝ) (hL : 0 < L)
    (hBF : -(((d : ℝ) + 1) ^ 2) / 4 < msq * L ^ 2) (φ : ℝ → ℝ) :
    IsRadialSolution d 0 0 msq L φ ↔
      ∃ A B : ℝ, ∀ r : ℝ, 0 < r →
        φ r = A * r ^ deltaMinus d msq L + B * r ^ deltaPlus d msq L := by sorry

end HolographicQuantumMatter
