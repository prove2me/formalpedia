-- Prove2me | Theorems.Thm_HeckeEis_exists_ne_zero_map_conjHom_eq_and_heckeH1_gammaH_bot_eq_smul_of_isEigensystemH1
-- name    : HeckeEis.exists_ne_zero_map_conjHom_eq_and_heckeH1_gammaH_bot_eq_smul_of_isEigensystemH1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/54255dfb-9e3a-5b3b-81d2-7256fbee692e
-- title:
--   From a Γ₀(N) eigensystem to a diamond-fixed eigenclass
-- statement:
--   Let $N$ be a non-zero natural number, $q$ a prime with $q \nmid N$, $S_0$ a set of natural numbers, $\kappa$ a field and $V$ a finite-dimensional $\kappa$-vector space carrying a representation $\rho$ of $\mathrm{GL}_2(\mathbb{Z}/q)$ such that every vector fixed by $\rho(g)$ for all $g \in \mathrm{SL}_2(\mathbb{Z}/q)$ is zero, and let $\lambda : \mathbb{N} \to \kappa$. Write $\rho'$ for the representation of $\Gamma_0(N)$ obtained from $\rho$ by the inclusion $\Gamma_0(N) \hookrightarrow \mathrm{SL}(2,\mathbb{Z})$, reduction modulo $q$ and $\mathrm{SL}_2 \to \mathrm{GL}_2$, and $\varphi_\ell = \rho(\mathrm{diag}(\ell,1))$ when $\ell \not\equiv 0 \bmod q$, $\varphi_\ell = \mathrm{id}$ otherwise. Assume [`HeckeEis.IsEigensystemH1`](def/Gamma0CoeffCohomologyEigen.html#L72) holds for $\rho'$, the adjusters $\varphi_\ell$, the excluded set $\{q\} \cup S_0$ and $\lambda$: there is a non-zero class $x$ in the quotient `coeffH1` of the coefficient cocycles by the coboundaries of $\rho'$ such that for every prime $\ell \nmid N$ outside $\{q\} \cup S_0$ some $\kappa$-linear endomorphism $T$ of `coeffH1` is induced at cochain level by `coeffHeckeFun` with adjuster $\varphi_\ell$ and satisfies $Tx = \lambda_\ell x$. Put $A$ for the restriction of $\rho'$ to the subgroup [`CohCarrier.GammaH N ⊥`](def/CohCarrier_Level.html#L133) of $\Gamma_0(N)$ (those elements whose diagonal unit class is trivial), regarded as an object of `Rep`. The conclusion asserts, first, that for each prime $\ell \nmid N$ outside $\{q\} \cup S_0$ the map $\varphi_\ell$ is a twist for the homomorphism `cTop N ⊥ ℓ`, i.e. $\varphi_\ell(A.\rho(\mathrm{conjL}\,s)a) = A.\rho(s)(\varphi_\ell a)$ for all $s$ in the subgroup $\Gamma^0(\ell)$-part `GammaHUpper N ⊥ ℓ` and all $a$; and, second, that there is a non-zero $y \in H^1(A)$ (Mathlib's `groupCohomology.H1`) which is fixed by all diamonds — for every $\sigma \in \Gamma_0(N)$ and every morphism $c$ from the restriction of $A$ along $\gamma \mapsto \sigma\gamma\sigma^{-1}$ to $A$ whose underlying map is $\rho(\bar\sigma)^{-1}$ on $V$, the induced map on $H^1$ sends $y$ to $y$ — and which satisfies $\mathrm{heckeH1}(\varphi_\ell)\,y = \lambda_\ell \cdot y$ for every such $\ell$.
--
--   This is the passage from an eigensystem on the hand-built coefficient cohomology of $\Gamma_0(N)$ to an eigenclass for the twisted transfer Hecke operators on the standard group cohomology $H^1$ of the restriction to the level-$\Gamma_H(N)$, $H = \bot$, subgroup, with the additional diamond-invariance needed downstream. It is used in the argument that separates the Steinberg and Eisenstein alternatives for such an eigensystem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_exists_ne_zero_map_conjHom_eq_and_heckeH1_gammaH_bot_eq_smul_of_isEigensystemH1.lean

import Mathlib
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_CohCarrier_Level
import Definitions.Def_GroupCohomology_TransferHecke
import Definitions.Def_GroupCohomology_DClassCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem HeckeEis.exists_ne_zero_map_conjHom_eq_and_heckeH1_gammaH_bot_eq_smul_of_isEigensystemH1
    (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) (S₀ : Set ℕ)
    (κ : Type) [Field κ]
    {V : Type} [AddCommGroup V] [Module κ V] [FiniteDimensional κ V]
    (ρ : Representation κ (CuspidalType.GL2 q) V)
    (hV : ∀ v : V, (∀ g : SL(2, ZMod q), ρ (Matrix.SpecialLinearGroup.toGL g) v = v) → v = 0)
    (lam : ℕ → κ)
    (hocc : HeckeEis.IsEigensystemH1 N (ρ.comp ((Matrix.SpecialLinearGroup.toGL.comp
            (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype))
      (fun ℓ : ℕ =>
        if h : ((ℓ : ZMod q) ≠ 0) then ρ (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h)) else LinearMap.id)
      (insert q S₀) lam) :
    ∃ hφ : ∀ i : {ℓ : ℕ // ℓ.Prime ∧ ¬ ℓ ∣ N ∧ ℓ ∉ insert q S₀},
        HeckeCohomology.IsTwist ⊤ (CohCarrier.GammaHUpper N ⊥ i.1) (HeckeCohomology.cTop N ⊥ i.1)
          (Rep.of ((ρ.comp ((Matrix.SpecialLinearGroup.toGL.comp
            (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype)).comp
              (Subgroup.inclusion (CohCarrier.GammaH_le_Gamma0 (M := N) (⊥ : Subgroup (ZMod N)ˣ)))))
          (if h : (((i.1 : ℕ) : ZMod q) ≠ 0) then ρ (CuspidalType.diagElem q (Units.mk0 ((i.1 : ℕ) : ZMod q) h))
            else LinearMap.id),
      ∃ y : groupCohomology.H1
          (Rep.of ((ρ.comp ((Matrix.SpecialLinearGroup.toGL.comp
            (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype)).comp
              (Subgroup.inclusion (CohCarrier.GammaH_le_Gamma0 (M := N) (⊥ : Subgroup (ZMod N)ˣ))))),
        y ≠ 0 ∧
        (∀ (σ : ↥(Gamma0 N))
            (c : Rep.res (CohCarrier.conjHom N (⊥ : Subgroup (ZMod N)ˣ) σ)
              (Rep.of ((ρ.comp ((Matrix.SpecialLinearGroup.toGL.comp
            (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype)).comp
              (Subgroup.inclusion (CohCarrier.GammaH_le_Gamma0 (M := N) (⊥ : Subgroup (ZMod N)ˣ))))) ⟶
              (Rep.of ((ρ.comp ((Matrix.SpecialLinearGroup.toGL.comp
            (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype)).comp
              (Subgroup.inclusion (CohCarrier.GammaH_le_Gamma0 (M := N) (⊥ : Subgroup (ZMod N)ˣ)))))),
            (∀ v : V, c.hom v = ρ (((Matrix.SpecialLinearGroup.toGL.comp
            (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype) σ)⁻¹ v) →
            groupCohomology.map (CohCarrier.conjHom N (⊥ : Subgroup (ZMod N)ˣ) σ) c 1 y = y) ∧
        ∀ i : {ℓ : ℕ // ℓ.Prime ∧ ¬ ℓ ∣ N ∧ ℓ ∉ insert q S₀},
          haveI : NeZero (i.1 : ℕ) := ⟨i.2.1.ne_zero⟩
          HeckeCohomology.heckeH1 ⊤ (CohCarrier.GammaHUpper N ⊥ i.1) (HeckeCohomology.cTop N ⊥ i.1)
            (Rep.of ((ρ.comp ((Matrix.SpecialLinearGroup.toGL.comp
            (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype)).comp
              (Subgroup.inclusion (CohCarrier.GammaH_le_Gamma0 (M := N) (⊥ : Subgroup (ZMod N)ˣ)))))
            (if h : (((i.1 : ℕ) : ZMod q) ≠ 0) then ρ (CuspidalType.diagElem q (Units.mk0 ((i.1 : ℕ) : ZMod q) h))
            else LinearMap.id)
            (hφ i) y = lam i.1 • y := by sorry
