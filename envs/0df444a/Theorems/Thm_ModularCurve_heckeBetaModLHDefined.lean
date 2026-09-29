-- Prove2me | Theorems.Thm_ModularCurve_heckeBetaModLHDefined
-- name    : ModularCurve.heckeBetaModLHDefined
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/fa61257f-3da3-597e-9f03-cba76e52b90e
-- title:
--   The degeneracy map q ↦ q^ℓ on q-expansion function fields
-- statement:
--   Let $K$ be a field, let $N \ge 1$, let $H'$ be a subgroup of $(\mathbb{Z}/N)^{\times}$ and let $\ell \ge 1$. Write $\Gamma_{H'}(N)$ for the subgroup [`CohCarrier.GammaH N H'`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}_2(\mathbb{Z})$, namely the image in $\mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H'$ under the homomorphism [`CohCarrier.gamma0Units N`](def/CohCarrier_Level.html#L121) from $\Gamma_0(N)$ to $(\mathbb{Z}/N)^{\times}$; and for a subgroup $\Gamma$ write $\bar F(\Gamma) =$ `qExpFunctionFieldC K Γ` for the intermediate field of $K((q))$ obtained by adjoining to $K$ the set `intFormRatiosC K Γ` of ratios of integral $q$-expansions attached to $\Gamma$. Let `qExpand K ℓ` be the ring endomorphism of $K((q))$ obtained by pushing a Laurent series forward along multiplication by $\ell$ on the exponent group $\mathbb{Z}$, i.e. the substitution $q \mapsto q^{\ell}$. The assertion is the predicate [`ModularCurve.HeckeBetaModLHDefined K N H' ℓ`](def/ModularCurve_XHDifferentialsModL.html#L143): for every $y \in \bar F(\Gamma_{H'}(N))$ one has $y(q^{\ell}) \in \bar F\bigl(\Gamma_{H'}(N) \cap \Gamma_0(N\ell)\bigr)$. No hypothesis beyond $N, \ell \ne 0$ is imposed; in particular $\ell$ need not be prime to $N$.
--
--   This is the second of the two degeneracy maps underlying the Hecke correspondence of index $\ell$ on the modular curve of level $\Gamma_{H'}(N)$, realised on $q$-expansion function fields: classically it comes from $f(\tau) \mapsto f(\ell\tau)$, which carries forms on $\Gamma_{H'}(N)$ to forms on $\Gamma_{H'}(N) \cap \Gamma_0(N\ell)$. It supplies the hypothesis 'the map $\beta$ is defined' to the later constructions of the Hecke action on differentials and on the associated correspondences at level $N\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckeBetaModLHDefined.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.heckeBetaModLHDefined
    (K : Type*) [Field K] (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ) (ℓ : ℕ) [NeZero ℓ] :
    ModularCurve.HeckeBetaModLHDefined K N H' ℓ := by sorry
