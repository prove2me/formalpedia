-- Prove2me | Theorems.Thm_NgoFL_transfer_factor_valuation
-- name    : NgoFL.transfer_factor_valuation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T03:00:04.031168+00:00
-- url     : https://prove2.me/theorems/f81fab56-5972-48a5-b7b3-37e00573011b
-- title:
--   1.11.3: $v(D_G) = v(D_H) + 2\,v(R^G_H)$, the transfer factor exponent
-- statement:
--   Let $F$ be a non-archimedean local field with additive valuation $v$ and residue cardinality
--   $q$, let $\Phi$ be the root system of a split reductive group $G$ over $F$, let $\Phi_H$ be the
--   root system of an endoscopic group $H$, and let $\Lambda$ be a set of representatives of the
--   pairs of opposite roots outside $\Phi_H$, so that $R^G_H = \prod_{\alpha\in\Lambda} d\alpha$.
--
--   Applying the valuation to the identity $D_G = \pm\, D_H \cdot (R^G_H)^2$ of 1.10.3, one obtains
--   for a point $a_H$ of the Cartan
--
--   $$ v\bigl(D_G(a_H)\bigr) \;=\; v\bigl(D_H(a_H)\bigr) \;+\; 2\, v\bigl(R^G_H(a_H)\bigr). $$
--
--   Ngo's normalizing factors are $\Delta_G(a) = q^{-v(D_G(a))/2}$ and $\Delta_H(a_H) =
--   q^{-v(D_H(a_H))/2}$, so the displayed identity is exactly the statement 1.11.3 that
--
--   $$ \Delta_H(a_H)\,\Delta_G(a)^{-1} \;=\; q^{\,r^G_{H,v}(a_H)}, \qquad
--      r^G_{H,v}(a_H) = v\bigl(R^G_H(a_H)\bigr), $$
--
--   and it is what allows the fundamental lemma to be written interchangeably as
--   $O^{\kappa}_a(\mathbf{1}_{\mathfrak{g}_v}, dt_v) = q^{\,r^G_{H,v}(a_H)}
--   SO_{a_H}(\mathbf{1}_{\mathfrak{h}_v}, dt_v)$ (Theoreme 1.11.1) or in the more familiar form
--   $\Delta_G(a) O^{\kappa}_a(\mathbf{1}_{\mathfrak{g}_v}, dt_v) = \Delta_H(a_H)
--   SO_{a_H}(\mathbf{1}_{\mathfrak{h}_v}, dt_v)$ (Theoreme 1, Introduction). The valuation form is
--   stated here because it is the form that remains meaningful when a discriminant vanishes, the
--   valuation then taking the value $+\infty$.
-- source:
--   Bao Chau Ngo, *Le lemme fondamental pour les algebres de Lie*, Publications mathematiques de l'IHES 111 (2010), 1-169, DOI 10.1007/s10240-010-0026-7, pp. 21-22, 1.11.3 (and Theoreme 1 of the Introduction, p. 2)

import Mathlib
import Definitions.Def_NgoEndoscopicDiscriminant

namespace NgoFL

theorem transfer_factor_valuation {ι M N F : Type*} [Field F] [AddCommGroup M] [Module F M]
    [AddCommGroup N] [Module F N] [Fintype ι] [DecidableEq ι] (P : RootPairing ι F M N)
    (v : AddValuation F (WithTop ℤ)) (s L : Finset ι) (hL : IsHalfSystem P sᶜ L) (x : N) :
    v (discriminant P x) = v (subDiscriminant P s x) + 2 • v (resultant P L x) := by sorry

end NgoFL
