-- Prove2me | Theorems.Thm_HolographicQuantumMatter_breitenlohner_freedman_bound
-- name    : HolographicQuantumMatter.breitenlohner_freedman_bound
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-27T17:46:52.127958+00:00
-- url     : https://prove2.me/theorems/7557f783-d6b7-4854-8d3e-8f1a82b4d4b8
-- title:
--   Breitenlohner–Freedman bound: real $\Delta$ iff $m^2L^2\ge-(d+1)^2/4$
-- statement:
--   Let $d\ge0$ and $m^2,L\in\mathbb R$. The mass–dimension relation (29) has a real solution $\Delta$ if and only if the Breitenlohner–Freedman bound holds:
--
--   $$\bigl(\exists\,\Delta\in\mathbb R:\ \Delta(\Delta-d-1)=m^2L^2\bigr)\iff m^2L^2\ge-\frac{(d+1)^2}{4}.$$
--
--   Equivalently, the scaling dimension becomes complex exactly when $m^2L^2<-D_{\rm eff}^2/4$ with $D_{\rm eff}=d+1$ (eq. (627) for AdS$_{d+2}$, where $z=1$), which signals an instability.
--
--   **Formalization Note** The boundary theory has $d$ spatial dimensions (so the bulk is $\mathrm{AdS}_{d+2}$), following the source's convention. The bulk mass squared is a real parameter $m^2$ (called `msq`), allowed to be negative; the source writes $(mL)^2$ for $m^2L^2$. Fields are real-valued functions of $r$; only their values on $r>0$ matter.
-- source:
--   Hartnoll, Lucas, Sachdev, *Holographic quantum matter*, arXiv:1612.07324v3, https://arxiv.org/abs/1612.07324, Section 6.2, p. 126, eq. (627), with $D_{\rm eff}=z+d$ from eq. (103) at $z=1$; see also p. 15

import Mathlib
import Definitions.Def_HolographicQuantumMatter_ScalarAdS

namespace HolographicQuantumMatter

theorem breitenlohner_freedman_bound (d : ℕ) (msq L : ℝ) :
    (∃ Δ : ℝ, Δ * (Δ - ((d : ℝ) + 1)) = msq * L ^ 2) ↔
      -(((d : ℝ) + 1) ^ 2) / 4 ≤ msq * L ^ 2 := by sorry

end HolographicQuantumMatter
