-- Prove2me | Theorems.Thm_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add
-- name    : NumberField.SUnits.finrank_invariants_repModP_sUnitsRep_tensor_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/0d182cc2-1fb3-516f-95e9-83fa272250f2
-- title:
--   Equivariant mod-p S-unit rank identity with coefficients
-- statement:
--   Let $E \subseteq K$ be number fields with $K/E$ Galois, write $G = K \simeq_{\mathrm{alg}[E]} K$ for its automorphism group, let $p$ be a prime with $\gcd(\#G, p) = 1$, let $S$ be a finite set of height-one primes of $\mathcal{O}_E$, and let $M$ be a representation of $G$ over $\mathbb{Z}/p$ that is finite-dimensional over $\mathbb{Z}/p$. Let $U =$ `sUnitsRep E K S` be the $\mathbb{Z}[G]$-module $\mathrm{Additive}(K^\times)$ restricted to the submodule of $S$-units of $K$ (the subgroup `sUnits E K S`), and let $U/pU$ and $U[p]$ denote the $\mathbb{Z}/p$-representations `repModP p` and `repTorsionP p` attached to it, namely the quotient by $p \cdot U$ and the $p$-torsion submodule. Then the $\mathbb{Z}/p$-dimension of the $G$-invariants of $(U/pU) \otimes M$ plus the dimension of $M^G$ equals the sum of three terms: the dimensions of the $G$-invariants of $P_\infty \otimes M$, of $P_S \otimes M$, and of $U[p] \otimes M$, where $P_\infty$ and $P_S$ are the permutation representations of $G$ on finitely supported $\mathbb{Z}/p$-valued functions on $\Sigma_{v \mid \infty \text{ of } E}\, G/D_{w(v)}$ and on $\Sigma_{v \in S}\, G/D_{w(v)}$ respectively, $w(v)$ being a chosen infinite place, resp. height-one prime, of $K$ above $v$ and $D_{w(v)}$ its stabiliser, resp. decomposition subgroup, in $G$.
--
--   This is the equivariant Dirichlet–Herbrand $S$-unit theorem in its mod-$p$ form, with coefficients: it records the identity $[U \otimes \mathbb{F}_p] + [\mathbf{1}] = [\mathbb{F}_p[S_\infty]] + [\mathbb{F}_p[S_f]] + [U[p]]$ in the Grothendieck group of $\mathbb{F}_p[G]$-modules, read through the additive invariant $X \mapsto \dim_{\mathbb{F}_p}(X \otimes M)^G$. It is used for the level-arithmetic input [`NumberField.LevelArith.finrank_invariants_unitsModP_tensor_add_finrank_invariants_eq`](thm.html#NumberField.LevelArith.finrank_invariants_unitsModP_tensor_add_finrank_invariants_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module IsDedekindDomain NumberField NumberField.LevelArith
open scoped Classical NumberField.LevelArith

theorem NumberField.SUnits.finrank_invariants_repModP_sUnitsRep_tensor_add
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    {p : ℕ} [Fact p.Prime] (hG : (Nat.card (K ≃ₐ[E] K)).Coprime p)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 E)))
    (M : Rep.{0} (ZMod p) (K ≃ₐ[E] K)) [FiniteDimensional (ZMod p) M] :
    Module.finrank (ZMod p) (repModP p (NumberField.SUnits.sUnitsRep E K S) ⊗ M : Rep.{0} (ZMod p) (K ≃ₐ[E] K)).ρ.invariants +
      Module.finrank (ZMod p) M.ρ.invariants =
      Module.finrank (ZMod p) (Rep.ofMulActionFinsupp (ZMod p) (K ≃ₐ[E] K)
          (Σ v : NumberField.InfinitePlace E, (K ≃ₐ[E] K) ⧸ NumberField.InfPlaceDecomp.decomp E K (NumberField.ArchIdele.above E K v)) ⊗ M :
          Rep.{0} (ZMod p) (K ≃ₐ[E] K)).ρ.invariants +
      Module.finrank (ZMod p) (Rep.ofMulActionFinsupp (ZMod p) (K ≃ₐ[E] K)
          (Σ v : S, (K ≃ₐ[E] K) ⧸ NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v)) ⊗ M :
          Rep.{0} (ZMod p) (K ≃ₐ[E] K)).ρ.invariants +
      Module.finrank (ZMod p) (repTorsionP p (NumberField.SUnits.sUnitsRep E K S) ⊗ M : Rep.{0} (ZMod p) (K ≃ₐ[E] K)).ρ.invariants := by sorry
