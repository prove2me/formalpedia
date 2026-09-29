-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_exists_jZeroNeronAtPDataOrdV22_of_children_of_neronExtension
-- name    : ModularCurve.JZeroNeronObjectAtP.exists_jZeroNeronAtPDataOrdV22_of_children_of_neronExtension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/f48301d8-47fd-5c51-bd86-b7da56672ff1
-- title:
--   From Néron object and extension to a v2.2 at-p datum
-- statement:
--   Fix $N_0\ge 1$ and a prime $p$ with $p\nmid N_0$, a valuation subring $A$ of an algebraic closure $\overline{\mathbb Q}$ of $\mathbb Q$ with $p$ a non-unit of $A$, a `LevelData` $\Lambda$ for $N_0,p,A$ (a relative group law over $\mathbb Z_{(p)}$ together with identifications of its generic and special points with $\mathrm{Pic}^0$ of the level-$N_0$ modular function field, written $JZero\,N_0$, and with its residue-field analogue) which satisfies `IsJacobian`, an object $O$ of `JZeroNeronObjectAtP` over $\Lambda$ (a smooth separated relative group scheme with connected fibres whose generic points are $JZero(N_0p)$, Galois- and Hecke-equivariantly, together with a toric rank, toric lifts and a component map), and a `NeronExtension` $F$ of $O$ over the subring cut out by the inertia-fixed field. Assume: each $x$ in $O.\mathrm{toricPts}\,m$ ($m>0$) is killed by both degeneracy pushforwards $JZero(N_0p)\to JZero\,N_0$; there is $c>0$ such that for $m>0$ any $x\in O.\mathrm{finPts}\,m$ killed by both pushforwards has $c\,x\in O.\mathrm{toricPts}\,m$; $\#O.\mathrm{toricPts}\,m=m^{O.\mathrm{toricRank}}$ and $\#O.\mathrm{finPts}\,m=m^{O.\mathrm{toricRank}+4g}$ for $m>0$, where $g$ is the genus of the residue-field modular function field $\mathrm{modularFunctionFieldC}$ of level $N_0$; $O.\mathrm{toricPts}\,m\le O.\mathrm{finPts}\,m$; for $m>0$ coprime to $p$ and $\sigma$ a Frobenius at $p$ for $A$, $\sigma^2$ acts as $p^2$ on $O.\mathrm{toricPts}\,m$, and (given the Hecke inputs and commutativity at level $N_0p$) $\sigma$ acts as $p\,T_p$ there; existence of homomorphisms $O.\mathrm{finPts}\,m\to JZero\,N_0\times JZero\,N_0$ for $m$ coprime to $p$ with kernel $O.\mathrm{toricPts}\,m$, image the $m$-torsion, compatible with the inclusions for $m\mid m'$, equivariant for $T_\ell$ with $\ell\nmid N_0p$ and for the decomposition subgroup; two level-lowering hypotheses producing, from an $\mathfrak m$-torsion point of $O.\mathrm{finPts}\,p$ outside $O.\mathrm{toricPts}\,p$ (for $\mathfrak m$ maximal in `HeckeAlg` containing $p$, in the second case with $T_p\notin\mathfrak m$), respectively `HasLowerLevelTorsion` for $JZero\,N_0$ and non-vanishing of its $\mathfrak m$-torsion; $\sigma x-x\in O.\mathrm{toricPts}\,m$ for $\sigma$ in inertia, $x$ $m$-torsion and $m$ coprime to $p$, and $\sigma x-x\in O.\mathrm{finPts}\,m$ for all $m>0$; Hecke stability of both families; and $O.\mathrm{toricPts}\,m\le \mathrm{toricMonodromyPart}\,p$ of the inertia subgroup for $m$ coprime to $p$. Then there exists a datum $\mathcal D$ of type `JZeroNeronAtPDataOrdV22` for $N_0,p,A$ whose toric and finite-part subgroups agree with $O.\mathrm{toricPts}\,m$ and $O.\mathrm{finPts}\,m$ for all $m>0$, whose toric rank is $O.\mathrm{toricRank}$, whose abelian rank is $2g$, all of whose elements of $\mathcal D.\mathrm{toric}\,0$ are killed by both degeneracy pushforwards, and for which some $c>0$ satisfies: any $x\in\mathcal D.\mathrm{fin}\,0$ killed by both pushforwards has $c\,x\in\mathcal D.\mathrm{toric}\,0$.
--
--   This is the assembly step that packages the special-fibre and torsion data of the Néron model of $J_0(N_0p)$ at $p$, in the presence of a Néron extension over the inertia-fixed base, into the structured at-$p$ ordinary datum of the v2.2 carrier used in the level-lowering arguments. It is cited by [`ModularCurve.JZeroNeronObjectAtP.exists_jZeroNeronAtPDataOrdV22_of_children`](thm.html#ModularCurve.JZeroNeronObjectAtP.exists_jZeroNeronAtPDataOrdV22_of_children), which supplies the Néron extension separately.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_exists_jZeroNeronAtPDataOrdV22_of_children_of_neronExtension.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_JZeroNeronAtPData
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_ToricMonodromyPart
import Definitions.Def_ModularCurve_JZeroNeronAtPDataOrdV22
import Definitions.Def_ModularCurve_ToricDescentData
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_NeronExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing
  AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.exists_jZeroNeronAtPDataOrdV22_of_children_of_neronExtension
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (F : O.NeronExtension)
    (hE1 : ∀ (m : ℕ), 0 < m → ∀ x ∈ O.toricPts m,
      degeneracyPushforwardPair N₀ p 0 x = 0 ∧ degeneracyPushforwardPair N₀ p 1 x = 0)
    (c : ℕ) (hc : 0 < c)
    (hE2 : ∀ (m : ℕ), 0 < m → ∀ x ∈ O.finPts m,
      degeneracyPushforwardPair N₀ p 0 x = 0 → degeneracyPushforwardPair N₀ p 1 x = 0 → c • x ∈ O.toricPts m)
    (hCT : ∀ (m : ℕ), 0 < m → Nat.card ↥(O.toricPts m) = m ^ O.toricRank)
    (hTF : ∀ (m : ℕ), O.toricPts m ≤ O.finPts m)
    (hCF : ∀ (m : ℕ), 0 < m → Nat.card ↥(O.finPts m) =
      m ^ (O.toricRank + 4 * genusFF (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N₀)))
    (hFS : ∀ (m : ℕ), 0 < m → m.Coprime p →
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ p →
        ∀ x ∈ O.toricPts m, σ • σ • x = ((p : ℤ) ^ 2) • x)
    (hFH : HeckeInputsAll (N₀ * p) → HeckeOperatorsCommuteBar (N₀ * p) →
      ∀ (m : ℕ), 0 < m → m.Coprime p →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ p →
          ∀ x ∈ O.toricPts m,
            σ • x = (letI := heckeModuleBar (N₀ * p); (((p : ℕ) : HeckeAlg) * heckeGen ⟨p, Fact.out⟩) • x))
    (hABQ : ∃ abq : ∀ m : ℕ, m.Coprime p → (↥(O.finPts m) →+ (JZero N₀ × JZero N₀)),
      (∀ (m : ℕ) (hm : m.Coprime p) (x : ↥(O.finPts m)), abq m hm x = 0 ↔ (x : JZero (N₀ * p)) ∈ O.toricPts m) ∧
      (∀ (m : ℕ) (hm : m.Coprime p),
        (abq m hm).range = (Submodule.torsionBy ℤ (JZero N₀ × JZero N₀) (m : ℤ)).toAddSubgroup) ∧
      (∀ (m m' : ℕ) (hm : m.Coprime p) (hm' : m'.Coprime p) (h : m ∣ m') (x : ↥(O.finPts m))
        (hx : (x : JZero (N₀ * p)) ∈ O.finPts m'), abq m' hm' ⟨x, hx⟩ = abq m hm x) ∧
      (∀ (m : ℕ) (hm : m.Coprime p) (ℓ : Nat.Primes), ¬ (ℓ : ℕ) ∣ N₀ * p → ∀ (x : ↥(O.finPts m))
        (hx : (letI := heckeModuleBar (N₀ * p); heckeGen ℓ • (x : JZero (N₀ * p))) ∈ O.finPts m),
        abq m hm ⟨_, hx⟩ = (letI := heckeModuleBar N₀; (heckeGen ℓ • (abq m hm x).1, heckeGen ℓ • (abq m hm x).2))) ∧
      (∀ (m : ℕ) (hm : m.Coprime p) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (hσ : σ ∈ A.decompositionSubgroup ℚ) (x : ↥(O.finPts m))
        (hx : σ • (x : JZero (N₀ * p)) ∈ O.finPts m),
        abq m hm ⟨_, hx⟩ = (σ • (abq m hm x).1, σ • (abq m hm x).2)))
    (hS1 : HeckeInputsAll (N₀ * p) → HeckeOperatorsCommuteBar (N₀ * p) →
      HeckeInputsAll N₀ → HeckeOperatorsCommuteBar N₀ →
        ∀ 𝔪 : Ideal HeckeAlg, 𝔪.IsMaximal → ((p : ℕ) : HeckeAlg) ∈ 𝔪 →
          ∀ x ∈ O.finPts p, (letI := heckeModuleBar (N₀ * p); x ∈ heckeTorsion (JZero (N₀ * p)) 𝔪) →
            x ∉ O.toricPts p →
              (letI := heckeModuleBar N₀; HasLowerLevelTorsion (primesOf (N₀ * p)) 𝔪 (JZero N₀)))
    (hS2 : HeckeInputsAll (N₀ * p) → HeckeOperatorsCommuteBar (N₀ * p) →
      HeckeInputsAll N₀ → HeckeOperatorsCommuteBar N₀ →
        ∀ 𝔪 : Ideal HeckeAlg, 𝔪.IsMaximal → ((p : ℕ) : HeckeAlg) ∈ 𝔪 → heckeGen ⟨p, Fact.out⟩ ∉ 𝔪 →
          ∀ x ∈ O.finPts p, (letI := heckeModuleBar (N₀ * p); x ∈ heckeTorsion (JZero (N₀ * p)) 𝔪) →
            x ∉ O.toricPts p →
              (letI := heckeModuleBar N₀; heckeTorsion (JZero N₀) 𝔪 ≠ ⊥))
    (hIU : ∀ (m : ℕ), m.Coprime p →
      ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x ∈ jZeroTorsion (N₀ * p) m, σ • x - x ∈ O.toricPts m)
    (hII : ∀ (m : ℕ), 0 < m →
      ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x ∈ jZeroTorsion (N₀ * p) m, σ • x - x ∈ O.finPts m)
    (hTH : ∀ (m : ℕ), 0 < m → letI := heckeModuleBar (N₀ * p);
      ∀ (t : HeckeAlg), ∀ x ∈ O.toricPts m, t • x ∈ O.toricPts m)
    (hFHk : ∀ (m : ℕ), 0 < m → letI := heckeModuleBar (N₀ * p);
      ∀ (t : HeckeAlg), ∀ x ∈ O.finPts m, t • x ∈ O.finPts m)
    (hTM : ∀ (m : ℕ), m.Coprime p → letI := heckeModuleBar (N₀ * p);
      O.toricPts m ≤ (toricMonodromyPart (J := JZero (N₀ * p)) p (A.inertiaSubgroupIn ℚ)).toAddSubgroup) :
    ∃ 𝓓 : JZeroNeronAtPDataOrdV22 N₀ p hpN₀ A hA,
      (∀ m : ℕ, 0 < m → 𝓓.toric m = O.toricPts m) ∧
      (∀ m : ℕ, 0 < m → 𝓓.fin m = O.finPts m) ∧
      𝓓.toricRank = O.toricRank ∧
      𝓓.abelianRank = 2 * genusFF (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N₀) ∧
      (∀ x ∈ 𝓓.toric 0, degeneracyPushforwardPair N₀ p 0 x = 0 ∧ degeneracyPushforwardPair N₀ p 1 x = 0) ∧
      (∃ c : ℕ, 0 < c ∧ ∀ x ∈ 𝓓.fin 0,
        degeneracyPushforwardPair N₀ p 0 x = 0 → degeneracyPushforwardPair N₀ p 1 x = 0 → c • x ∈ 𝓓.toric 0) := by sorry
