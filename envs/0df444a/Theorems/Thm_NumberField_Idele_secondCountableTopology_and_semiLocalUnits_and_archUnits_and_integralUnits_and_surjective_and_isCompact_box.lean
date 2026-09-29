-- Prove2me | Theorems.Thm_NumberField_Idele_secondCountableTopology_and_semiLocalUnits_and_archUnits_and_integralUnits_and_surjective_and_isCompact_box
-- name    : NumberField.Idele.secondCountableTopology_and_semiLocalUnits_and_archUnits_and_integralUnits_and_surjective_and_isCompact_box
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/c818b58d-7af6-539d-94dc-e7e7e1232aff
-- title:
--   Semi-local coordinates on A_L^×: topology, surjectivity, compact boxes
-- statement:
--   Let $K$ and $L$ be number fields with a fixed $K$-algebra structure on $L$. The theorem asserts eight things simultaneously about the unit group $(\mathbb{A}_L)^\times$ of the adele ring of $L$ and its semi-local coordinates. First, $(\mathbb{A}_L)^\times$ is second countable. Second, for every height one prime $v$ of $\mathcal{O}_K$ the group $(L \otimes_K K_v)^\times$ is a topological group which is locally compact, Hausdorff and second countable, and the subgroup `integralUnits K L v` — those units of $L \otimes_K K_v$ which, together with their inverses, lie in the image of $\mathcal{O}_L \otimes_{\mathcal{O}_K} \mathcal{O}_{K_v}$ under `HeightOneSpectrum.tensorAdicCompletionIntegersTo` — is compact and open. Third, for every infinite place $v$ of $K$ the group $(\prod_{w \mid v} L_w)^\times$, the product running over the places $w$ of $L$ with $w|_K = v$, is likewise a locally compact, Hausdorff, second countable topological group. Fourth, for every finite set $S_f$ of height one primes of $\mathcal{O}_K$, the set of ideles $t$ with `semiLocalIdele K L v t` integral for all $v \notin S_f$ is open; here `semiLocalIdele K L v` sends a unit idele to its finite part, collects the components at the places $w \mid v$, and transports them through the base-change isomorphism into $(L \otimes_K K_v)^\times$. Fifth, joint surjectivity: given a finite set $S_f$, an arbitrary family $y$ of units at the infinite places of $K$ and a family $x$ of units at the finite places with $x_v$ integral for $v \notin S_f$, there is a unit idele $t$ of $L$ with `archSemiLocalIdele K L v t` $= y_v$ for all infinite $v$ (the infinite part of $t$ restricted to the places above $v$) and `semiLocalIdele K L v t` $= x_v$ for all finite $v$. Sixth, compactness of boxes: for families of compact sets $D_v \subseteq (\prod_{w\mid v} L_w)^\times$ ($v$ infinite) and $C_v \subseteq (L \otimes_K K_v)^\times$ ($v$ finite) with $C_v$ equal to `integralUnits K L v` for all but finitely many $v$, the set of $t$ whose coordinates satisfy $t_v \in D_v$ and $t_v \in C_v$ is compact. Seventh, for each finite $v$ the subgroup `normOneUnits K L v`, the kernel of the composite of the $K_v$-algebra norm $L \otimes_K K_v \to K_v$ with the valuation of $K_v$, is closed. Eighth, for each infinite $v$ the subgroup `archNormOneUnits K L v`, the kernel of the composite of the $K_v$-algebra norm $\prod_{w \mid v} L_w \to K_v$ with the absolute value $K_v \to \mathbb{R}$, is closed.
--
--   This packages the topological description of the idele group of $L$ in the restricted-product coordinates obtained by grouping the places of $L$ over those of $K$: second countability, local compactness of the semi-local factors, compact-openness of the integral unit subgroups, surjectivity onto restricted products and compactness of boxes. In this form it supplies the hypotheses needed to factorise a Haar measure on $(\mathbb{A}_L)^\times$ over the semi-local places, and it is used by the transversal-measure and twisted orbital integral computations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_Idele_secondCountableTopology_and_semiLocalUnits_and_archUnits_and_integralUnits_and_surjective_and_isCompact_box.lean

import Definitions.Def_AutomorphicForm_TransversalMeasure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm.TransversalMeasure
open scoped TensorProduct TensorProduct.RightActions

theorem NumberField.Idele.secondCountableTopology_and_semiLocalUnits_and_archUnits_and_integralUnits_and_surjective_and_isCompact_box
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ ∧
    (∀ v : HeightOneSpectrum (𝓞 K),
      IsTopologicalGroup (L ⊗[K] v.adicCompletion K)ˣ ∧ LocallyCompactSpace (L ⊗[K] v.adicCompletion K)ˣ ∧
        T2Space (L ⊗[K] v.adicCompletion K)ˣ ∧ SecondCountableTopology (L ⊗[K] v.adicCompletion K)ˣ ∧
        IsCompact (integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) ∧ IsOpen (integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ)) ∧
    (∀ v : InfinitePlace K,
      IsTopologicalGroup (∀ w : v.Extension L, w.1.Completion)ˣ ∧ LocallyCompactSpace (∀ w : v.Extension L, w.1.Completion)ˣ ∧
        T2Space (∀ w : v.Extension L, w.1.Completion)ˣ ∧ SecondCountableTopology (∀ w : v.Extension L, w.1.Completion)ˣ) ∧
    (∀ Sf : Finset (HeightOneSpectrum (𝓞 K)),
      IsOpen {t : (AdeleRing (𝓞 L) L)ˣ | ∀ v, v ∉ Sf → semiLocalIdele K L v t ∈ integralUnits K L v}) ∧
    (∀ (Sf : Finset (HeightOneSpectrum (𝓞 K))) (y : ∀ v : InfinitePlace K, (∀ w : v.Extension L, w.1.Completion)ˣ)
      (x : ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ),
      (∀ v, v ∉ Sf → x v ∈ integralUnits K L v) →
        ∃ t : (AdeleRing (𝓞 L) L)ˣ, (∀ v, archSemiLocalIdele K L v t = y v) ∧ ∀ v, semiLocalIdele K L v t = x v) ∧
    (∀ (D : ∀ v : InfinitePlace K, Set (∀ w : v.Extension L, w.1.Completion)ˣ) (C : ∀ v : HeightOneSpectrum (𝓞 K), Set (L ⊗[K] v.adicCompletion K)ˣ),
      (∀ v, IsCompact (D v)) → (∀ v, IsCompact (C v)) →
        {v | C v ≠ (integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ)}.Finite →
        IsCompact {t : (AdeleRing (𝓞 L) L)ˣ | (∀ v, archSemiLocalIdele K L v t ∈ D v) ∧ ∀ v, semiLocalIdele K L v t ∈ C v}) ∧
    (∀ v : HeightOneSpectrum (𝓞 K), IsClosed (normOneUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ)) ∧
    (∀ v : InfinitePlace K, IsClosed (archNormOneUnits K L v : Set (∀ w : v.Extension L, w.1.Completion)ˣ)) := by sorry
