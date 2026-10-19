-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_LocalComparison_comparison_step_left
-- name    : OAI.CirculantHadamard.LocalComparison.comparison_step_left
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:53:34.470828+00:00
-- url     : https://prove2.me/theorems/4f0f76b9-5597-4980-8578-b8e409fc9710
-- title:
--   Inductive step of the local comparison
-- statement:
--   Let $A$ be a domain, $S$ a local domain with residue map $\mathrm{res}$, $\varphi:A\to S$ a ring homomorphism, $p\in\mathbb N$ with $p$ prime in $A$, and $\varepsilon$ the augmentation of the group algebra $A[\mathbb Z/n]$. Say $x\sim y$ if $x=wy$ for a unit $w$ of $S$ with $\mathrm{res}(w)=1$. Let $p\ne0$ in $A$, let $\pi$ be the projection $A[\mathbb Z/p^{e+2}]\to A[\mathbb Z/p^{e+1}]$, and let $v,v'$ be ring homomorphisms from these group algebras to $S$ with $v=\varphi$ on scalars and $v\circ\pi=v'$. Suppose $F,K\in A[\mathbb Z/p^{e+2}]$ satisfy
--   $$
--   FK=p^{e+2}\,b
--   $$
--   with $b$ a unit, and $\pi(F)=p\,F'$. If the comparison holds at level $e+1$ for every pair $U,V$ with $UV=p^{e+1}b$, then $v'(F)\sim\varphi(\varepsilon(F))$ and $v'(K)\sim\varphi(\varepsilon(K))$.
--
--   Dividing a projected factor by $p$ lowers the exponent and lets the comparison pass from level $e+1$ to level $e+2$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/LocalComparisonInduction.lean#L90-L130

import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalDVR
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_IntegerTwoLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicPolynomial
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedConjugation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicIntegerEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_DyadicRemainder
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedEisenstein
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_OrderHalving
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryBlocks
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryCoefficients
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicRings
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_PrimeComponents
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_PrimeCharacterEvaluations
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalizationMaps
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalization
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_AlternatingProducts
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryProductTransport
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_FirstOrderResidue
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryResidue
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalFamily
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_ResidueOneAssociation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicLocalBase
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicAwayLocal

open OAI OAI.CirculantHadamard OAI.CirculantHadamard.LocalComparison
universe uA uS
open CyclicRing
variable {A : Type uA} {S : Type uS} [CommRing A] [IsDomain A]
  [CommRing S] [domainS : IsDomain S] [IsLocalRing S]

omit domainS in
theorem OAI.CirculantHadamard.LocalComparison.comparison_step_left [IsDomain S] (p e : ℕ) (φ : A →+* S)
    (hp : (p : A) ≠ 0)
    (v : Elem A (p ^ (e + 1)) →+* S)
    (v' : Elem A (p ^ (e + 2)) →+* S)
    (vscalar : ∀ a : A, v (scalar (p ^ (e + 1)) a) = φ a)
    (vq : ∀ F : Elem A (p ^ (e + 2)),
      v (cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) F) = v' F)
    (b : Aˣ) (F K : Elem A (p ^ (e + 2)))
    (hFK : F * K = scalar (p ^ (e + 2)) ((p : A) ^ (e + 2) * (b : A)))
    (F' : Elem A (p ^ (e + 1)))
    (hF : cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) F =
      scalar (p ^ (e + 1)) (p : A) * F')
    (ih : ∀ U V : Elem A (p ^ (e + 1)),
      U * V = scalar (p ^ (e + 1)) ((p : A) ^ (e + 1) * (b : A)) →
        ResidueOneAssociated (IsLocalRing.residue S) (v U)
          (φ (augmentation (p ^ (e + 1)) U)) ∧
        ResidueOneAssociated (IsLocalRing.residue S) (v V)
          (φ (augmentation (p ^ (e + 1)) V))) :
    ResidueOneAssociated (IsLocalRing.residue S) (v' F)
      (φ (augmentation (p ^ (e + 2)) F)) ∧
    ResidueOneAssociated (IsLocalRing.residue S) (v' K)
      (φ (augmentation (p ^ (e + 2)) K)) := by sorry
