-- Prove2me | Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_unitsAct_map_genuineBaseChange
-- name    : M4aHerbrand.IdeleGaloisDescent.unitsAct_map_genuineBaseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/6f61ca8a-aa04-5a43-a05d-74fe8f5a5c72
-- title:
--   Genuine idèle base change is Galois-equivariant in a tower
-- statement:
--   Let $E$, $F$, $M$ be number fields with $E$-algebra structures on $F$ and $M$, an $F$-algebra structure on $M$ forming a scalar tower over $E$, and with both $F/E$ and $M/E$ Galois. Let $D$ be an idèle Galois descent datum for $F$ over $E$, that is, a monoid homomorphism from $F \simeq_{\mathrm{alg}[E]} F$ to the ring automorphisms of $\mathrm{AdeleRing}\,(\mathcal O_F)\,F$ whose value at $g$ acts on the diagonal image of $F$ by $g$ and is continuous; let $D''$ be such a datum for $M$ over $E$. Let $\sigma \colon M \simeq_{\mathrm{alg}[E]} M$ and let $x$ be a unit of $\mathrm{AdeleRing}\,(\mathcal O_F)\,F$. Write $\beta =$ the ring homomorphism component `β` of `genuineBaseChange F M`, namely $\mathrm{genuine}\beta\,F\,M \colon \mathrm{AdeleRing}\,(\mathcal O_F)\,F \to \mathrm{AdeleRing}\,(\mathcal O_M)\,M$, which carries the diagonal image of $f \in F$ to the diagonal image of its image in $M$ and induces an isomorphism $\mathrm{AdeleRing}\,(\mathcal O_F)\,F \otimes_F M \cong \mathrm{AdeleRing}\,(\mathcal O_M)\,M$ sending $1 \otimes m$ to the diagonal image of $m$. The conclusion is that the automorphism of the unit group induced by $D''$ at $\sigma$, applied to $\beta(x)$, equals $\beta$ applied to the automorphism induced by $D$ at $\mathrm{restrictNormalHom}\,F\,\sigma$, the restriction of $\sigma$ to $F$, applied to $x$.
--
--   This is the $\mathrm{Gal}(M/E)$-equivariance of the idèle base change $\mathbb I_F \to \mathbb I_M$ along the restriction surjection $\mathrm{Gal}(M/E) \to \mathrm{Gal}(F/E)$, so that base change is a morphism of Galois modules from the restriction of the idèles of $F$ to the idèles of $M$. It is the compatibility required for inflation along a tower in idèle cohomology, and is used in the construction of $2$-cocycles valued in $S$-units with prescribed local behaviour and in the associated capitulation arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_IdeleGaloisDescent_unitsAct_map_genuineBaseChange.lean

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField M4aHerbrand M4aHerbrand.GenuineDescent

theorem M4aHerbrand.IdeleGaloisDescent.unitsAct_map_genuineBaseChange
    (E F M : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field M] [NumberField M]
    [Algebra E F] [Algebra E M] [Algebra F M] [IsScalarTower E F M] [IsGalois E F] [IsGalois E M]
    (D : IdeleGaloisDescent (𝓞 F) E F) (D'' : IdeleGaloisDescent (𝓞 M) E M)
    (σ : M ≃ₐ[E] M) (x : (AdeleRing (𝓞 F) F)ˣ) :
    D''.unitsAct σ (Units.map (genuineBaseChange F M).β.toMonoidHom x) =
      Units.map (genuineBaseChange F M).β.toMonoidHom (D.unitsAct (AlgEquiv.restrictNormalHom F σ) x) := by sorry
