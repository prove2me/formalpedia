-- Prove2me | Theorems.Thm_Leopoldt_continuous_hom_zp_eq
-- name    : Leopoldt.continuous_hom_zp_eq
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T02:41:44.771986+00:00
-- url     : https://prove2.me/theorems/95c95035-e4cc-4427-9c3d-bae7c31f8c6c
-- title:
--   Continuous homomorphisms $\mathbb{Z}_p \to U$ are determined by the image of $1$
-- statement:
--   Let $K$ be a number field, $p$ a prime and $U = \prod_{\wp \mid p} \mathcal{O}_\wp^\times$ the semilocal units, a Hausdorff topological group. If $f, g : \mathbb{Z}_p \to U$ are continuous group homomorphisms (from the additive group of $\mathbb{Z}_p$) with $f(1) = g(1)$, then $f = g$.
--
--   Indeed $f$ and $g$ agree on $\mathbb{Z} \subset \mathbb{Z}_p$, which is dense, and the locus where two continuous maps into a Hausdorff space agree is closed.
-- source:
--   Density of Z in Z_p (Mathlib PadicInt.denseRange_intCast); semilocal units U as in arXiv:1105.4544 Section 1.1 and mission definition file Def_LeopoldtDefect

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem continuous_hom_zp_eq (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]
    {f g : Multiplicative ℤ_[p] →* SemilocalUnits p K} (hf : Continuous f) (hg : Continuous g)
    (h : f (Multiplicative.ofAdd 1) = g (Multiplicative.ofAdd 1)) : f = g := by sorry
end Leopoldt
