-- Prove2me | Theorems.Thm_M4aHerbrand_nonempty_unitIdelesTrivialOn_iso_pi_coind_localIntegerUnits
-- name    : M4aHerbrand.nonempty_unitIdelesTrivialOn_iso_pi_coind_localIntegerUnits
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/c97bfeb2-7993-59b1-8f09-2d90b8831c9b
-- title:
--   Unit idèles trivial on T as coinduced local units
-- statement:
--   Let $E \subseteq F$ be number fields with $F/E$ Galois, let $D$ be an idèle Galois descent datum for $\mathbb I_F =$ `AdeleRing (𝓞 F) F`, that is, a continuous action of $\mathrm{Gal}(F/E)$ on $\mathbb I_F$ by ring automorphisms extending the action on $F$, and let $T$ be a set of height-one primes of $\mathcal O_F$ which is a union of fibres over $\mathcal O_E$ (if $w$ and $w'$ lie under the same prime of $\mathcal O_E$ then $w \in T \iff w' \in T$). Assume $\mathrm{Gal}(F/E)$ acts multiplicatively and distributively on the subgroup $U_F^T \le \mathbb I_F^\times$ of units whose infinite part is $1$, whose component at each $w \in T$ is $1$, and which together with their inverses are integral at every prime outside $T$, and assume this action is induced by $D$, i.e. $g \cdot x$ has underlying unit $D.\mathrm{unitsAct}\,g\,x$. Then there exists an isomorphism, in the category of $\mathbb Z[\mathrm{Gal}(F/E)]$-representations, between $U_F^T$ written additively and the product, over those primes $v$ of $\mathcal O_E$ lying under no element of $T$, of the representations coinduced along the inclusion of the decomposition subgroup of the chosen prime above $v$ from the units of the ring of integers of the completion of $F$ at that prime. The conclusion asserts only the nonemptiness of the type of such isomorphisms.
--
--   This is the adelic dictionary identifying the group of $T$-unit idèles $U_F^T$ with $\prod_{v \notin T_E} \mathrm{Coind}^{\mathrm{Gal}(F/E)}_{D_w} \mathcal O_w^\times$, the form in which Shapiro's lemma and the computation of the cohomology of local units become available. It is used to transport that computation to $U_F^T$, in the vanishing of the group cohomology of $U_F^T$ in the unramified case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_nonempty_unitIdelesTrivialOn_iso_pi_coind_localIntegerUnits.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_FiniteSIdeleModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand CategoryTheory
open scoped NumberField.PlaceDecomp

theorem M4aHerbrand.nonempty_unitIdelesTrivialOn_iso_pi_coind_localIntegerUnits
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F) (T : Set (HeightOneSpectrum (𝓞 F)))
    (hTst : ∀ w w' : HeightOneSpectrum (𝓞 F), w.under (𝓞 E) = w'.under (𝓞 E) → (w ∈ T ↔ w' ∈ T))
    [MulDistribMulAction (F ≃ₐ[E] F) (unitIdelesTrivialOn (𝓞 F) F T)]
    (hactU : ∀ (g : F ≃ₐ[E] F) (x : unitIdelesTrivialOn (𝓞 F) F T),
      ((g • x : unitIdelesTrivialOn (𝓞 F) F T) : (AdeleRing (𝓞 F) F)ˣ) = D.unitsAct g x) :
    Nonempty (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (unitIdelesTrivialOn (𝓞 F) F T) ≅
      GroupCohomology.RepPi.obj (fun v : {v : HeightOneSpectrum (𝓞 E) // ∀ w ∈ T, w.under (𝓞 E) ≠ v} =>
        Rep.coind (NumberField.FiniteSIdele.D E F v.1).subtype (NumberField.FiniteSIdele.localIntegerUnits E F v.1))) := by sorry
