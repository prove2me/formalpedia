-- Prove2me | Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_measurePreserving_act_adelicAddHaar
-- name    : M4aHerbrand.IdeleGaloisDescent.measurePreserving_act_adelicAddHaar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/9e1d5133-f058-5892-80c3-4d944e3ef8cb
-- title:
--   Haar measure on A_L is invariant under a descent datum
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, and let $D$ be an element of [`M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L`](def/M4aHerbrand_IdeleClassVocab.html#L28), that is: a monoid homomorphism $\mathrm{act}$ from the group $L \simeq_{\mathrm{alg}[K]} L$ of $K$-algebra automorphisms of $L$ to the group of ring automorphisms of the adele ring $\mathbb{A}_L =$ `AdeleRing (𝓞 L) L`, subject to the compatibility $\mathrm{act}(g)(\iota(x)) = \iota(g x)$ for all $g$ and all $x \in L$, where $\iota \colon L \to \mathbb{A}_L$ is the structure map, and to the requirement that $\mathrm{act}(g)$ be continuous for every $g$. Let $\sigma$ be a $K$-algebra automorphism of $L$. The assertion is that the underlying map of the ring automorphism $D.\mathrm{act}\,\sigma$ of $\mathbb{A}_L$ is measure preserving for the additive Haar measure `adelicAddHaar (𝓞 L) L` on $\mathbb{A}_L$, taken for the Borel $\sigma$-algebra of the adelic topology, in source and target: the map is measurable and its pushforward of that Haar measure is again that Haar measure.
--
--   This is the statement that a continuous automorphism of $\mathbb{A}_L$ of finite order has module $1$, specialised to the automorphisms coming from a Galois descent datum on the adeles. It licenses the change of variables $q \mapsto \sigma q$ in adelic integrals, and is used in the computation of twisted orbital integrals for unipotent elements of $\mathrm{GL}_2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_IdeleGaloisDescent_measurePreserving_act_adelicAddHaar.lean

import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem M4aHerbrand.IdeleGaloisDescent.measurePreserving_act_adelicAddHaar
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) :
    MeasurePreserving (D.act σ) (adelicAddHaar (𝓞 L) L) (adelicAddHaar (𝓞 L) L) := by sorry
