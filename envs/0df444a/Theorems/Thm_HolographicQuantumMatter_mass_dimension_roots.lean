-- Prove2me | Theorems.Thm_HolographicQuantumMatter_mass_dimension_roots
-- name    : HolographicQuantumMatter.mass_dimension_roots
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-27T17:45:01.642515+00:00
-- url     : https://prove2.me/theorems/a790fba7-14f8-4c18-9ab1-0ee5341fe7aa
-- title:
--   The two roots $\Delta_\pm$ of the mass–dimension relation
-- statement:
--   Let $d\ge0$, $L\in\mathbb R$ and $m^2\in\mathbb R$ satisfy $m^2L^2\ge-\frac{(d+1)^2}{4}$. Define
--
--   $$\Delta_\pm=\frac{d+1}{2}\pm\sqrt{\frac{(d+1)^2}{4}+m^2L^2}.$$
--
--   Then for every real $\Delta$,
--
--   $$\Delta(\Delta-d-1)=m^2L^2\iff \Delta=\Delta_+\ \text{or}\ \Delta=\Delta_- .$$
--
--   The source notes that for a given bulk mass, (29) has two solutions $\Delta_\pm$; the larger one $\Delta_+$ is the dimension in standard quantization and $\Delta_-$ in alternate quantization.
--
--   **Formalization Note** The boundary theory has $d$ spatial dimensions (so the bulk is $\mathrm{AdS}_{d+2}$), following the source's convention. The bulk mass squared is a real parameter $m^2$ (called `msq`), allowed to be negative; the source writes $(mL)^2$ for $m^2L^2$. Fields are real-valued functions of $r$; only their values on $r>0$ matter.
-- source:
--   Hartnoll, Lucas, Sachdev, *Holographic quantum matter*, arXiv:1612.07324v3, https://arxiv.org/abs/1612.07324, Section 1.6.2, p. 10 (text after eq. (30)) and p. 15 (alternate quantization)

import Mathlib
import Definitions.Def_HolographicQuantumMatter_ScalarAdS

namespace HolographicQuantumMatter

theorem mass_dimension_roots (d : ℕ) (msq L : ℝ)
    (hBF : -(((d : ℝ) + 1) ^ 2) / 4 ≤ msq * L ^ 2) (Δ : ℝ) :
    Δ * (Δ - ((d : ℝ) + 1)) = msq * L ^ 2 ↔
      Δ = deltaPlus d msq L ∨ Δ = deltaMinus d msq L := by sorry

end HolographicQuantumMatter
