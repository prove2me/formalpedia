-- Prove2me | Theorems.Thm_ModularCurve_exists_addEquiv_appendixComponentGroup_x0MqResolvedTable_apply_eq_componentGroupProj
-- name    : ModularCurve.exists_addEquiv_appendixComponentGroup_x0MqResolvedTable_apply_eq_componentGroupProj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/33fd8d17-42f1-576c-aef3-61679ff24fb8
-- title:
--   Explicit isomorphism of the Mazur–Rapoport and cycle component groups
-- statement:
--   Let $\iota$ be a finite type, let $e : \iota \to \mathbb{N}$ satisfy $0 < e(x)$ for all $x$, and fix $s_0 \in \iota$. Consider the table `x0MqResolvedTable e` on the vertex type $\mathrm{Fin}\,2 \sqcup \bigl(\Sigma_{x}\ \mathrm{Fin}(e(x)-1)\bigr)$, all multiplicities $1$ and intersection numbers $\mathrm{inter}(i,j) = \mathrm{x0MqAdj}(i,j) - \delta_{ij}\sum_{j'} \mathrm{x0MqAdj}(i,j')$. Its degree-zero sublattice is the kernel of $a \mapsto \sum_i a(i)$, and `AppendixComponentGroup` is that sublattice modulo the part of the range of `intersectionAlpha` lying in it; on the other side, `componentGroup e` is $\mathrm{Hom}_{\mathbb{Z}}(\mathrm{characterLattice}\,\iota, \mathbb{Z})$, where $\mathrm{characterLattice}\,\iota = \ker(\sum_x \mathrm{proj}_x)$, modulo the range of `gramMap e`, the restriction of `widthPairing e` to that lattice. The assertion is that there is an isomorphism $\psi$ of additive groups between the two such that for every $a$ in the degree-zero sublattice, $\psi$ of the class of $a$ is the class of the functional obtained by restricting $\sum_{s}\bigl(\sum_{k < e(s)-1}(k+1)\,a(\mathrm{inr}(s,k))\bigr)\mathrm{proj}_s + e(s_0)\,a(\mathrm{inl}\,1)\,\mathrm{proj}_{s_0}$ to the character lattice; and, moreover, $\mathrm{Pi.single}(\mathrm{inl}\,1)\,1 - \mathrm{Pi.single}(\mathrm{inl}\,0)\,1$ lies in the degree-zero sublattice and $\psi$ sends its class to the class of $e(s_0)\,\mathrm{proj}_{s_0}$ restricted to the character lattice.
--
--   This is the duality between the critical group of a graph presented by its Laplacian on degree-zero vertex divisors and the cycle lattice modulo its Gram pairing, made explicit for the two-vertex multigraph on $\iota$ with the edge $s$ subdivided into $e(s)$ unit edges, which is the dual graph of the resolved special fibre under consideration; the second clause records the image of the difference of the two branch classes. It is used in the Deligne–Rapoport model package to convert vanishing of a composite with the component-group projection into membership in the range of the intersection map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_addEquiv_appendixComponentGroup_x0MqResolvedTable_apply_eq_componentGroupProj.lean

import Mathlib
import Definitions.Def_ModularCurve_X0MqResolvedTable
import Definitions.Def_ModularCurve_ComponentGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve MazurRapoportAppendix

theorem ModularCurve.exists_addEquiv_appendixComponentGroup_x0MqResolvedTable_apply_eq_componentGroupProj
    {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → ℕ) (he : ∀ x, 0 < e x) (s₀ : ι) :
    ∃ ψ : AppendixComponentGroup (x0MqResolvedTable e) ≃+ componentGroup e,
      (∀ (a : X0MqComponents e → ℤ) (ha : a ∈ degreeZeroSublattice (x0MqResolvedTable e)),
        ψ (appendixComponentGroupClass (x0MqResolvedTable e) ⟨a, ha⟩) =
          componentGroupProj e
            (((∑ s : ι, (∑ k : Fin (e s - 1), ((k : ℤ) + 1) * a (Sum.inr ⟨s, k⟩)) •
                  (LinearMap.proj s : (ι → ℤ) →ₗ[ℤ] ℤ)) +
                ((e s₀ : ℤ) * a (Sum.inl 1)) • (LinearMap.proj s₀ : (ι → ℤ) →ₗ[ℤ] ℤ)).comp
              (characterLattice ι).subtype)) ∧
      ∃ hb : (Pi.single (Sum.inl 1) 1 - Pi.single (Sum.inl 0) 1 : X0MqComponents e → ℤ) ∈
          degreeZeroSublattice (x0MqResolvedTable e),
        ψ (appendixComponentGroupClass (x0MqResolvedTable e) ⟨_, hb⟩) =
          componentGroupProj e ((e s₀ : ℤ) •
            (LinearMap.proj s₀ : (ι → ℤ) →ₗ[ℤ] ℤ).comp (characterLattice ι).subtype) := by sorry
