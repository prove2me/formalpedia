-- Prove2me | Theorems.Thm_HolographicQuantumMatter_d_add_one_sub_delta
-- name    : HolographicQuantumMatter.d_add_one_sub_delta
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-27T17:45:31.224716+00:00
-- url     : https://prove2.me/theorems/85347cbb-bbcc-4f37-8179-4ea2ca08d460
-- title:
--   $d+1-\Delta_\pm=\Delta_\mp$
-- statement:
--   Let $d\ge0$ and $m^2,L\in\mathbb R$, and let $\Delta_\pm=\frac{d+1}{2}\pm\sqrt{\frac{(d+1)^2}{4}+m^2L^2}$. Then
--
--   $$d+1-\Delta_+=\Delta_-\qquad\text{and}\qquad d+1-\Delta_-=\Delta_+ .$$
--
--   In the expansion (28) the source term scales as $r^{d+1-\Delta}$ and the response as $r^{\Delta}$; this identity says the two exponents are exactly $\Delta_-$ and $\Delta_+$.
--
--   **Formalization Note** The boundary theory has $d$ spatial dimensions (so the bulk is $\mathrm{AdS}_{d+2}$), following the source's convention. The bulk mass squared is a real parameter $m^2$ (called `msq`), allowed to be negative; the source writes $(mL)^2$ for $m^2L^2$. Fields are real-valued functions of $r$; only their values on $r>0$ matter. No bound on $m^2L^2$ is assumed: below the Breitenlohner–Freedman bound the square root takes Lean's junk value $0$, and the identity still holds.
-- source:
--   Hartnoll, Lucas, Sachdev, *Holographic quantum matter*, arXiv:1612.07324v3, https://arxiv.org/abs/1612.07324, Section 1.6.2, p. 10: "Note that $d+1-\Delta_\pm=\Delta_\mp$."

import Mathlib
import Definitions.Def_HolographicQuantumMatter_ScalarAdS

namespace HolographicQuantumMatter

theorem d_add_one_sub_delta (d : ℕ) (msq L : ℝ) :
    ((d : ℝ) + 1) - deltaPlus d msq L = deltaMinus d msq L ∧
      ((d : ℝ) + 1) - deltaMinus d msq L = deltaPlus d msq L := by sorry

end HolographicQuantumMatter
