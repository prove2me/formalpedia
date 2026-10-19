-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_LocalComparison_comparison_base
-- name    : OAI.CirculantHadamard.LocalComparison.comparison_base
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:52:52.637844+00:00
-- url     : https://prove2.me/theorems/5d67dc8c-e62b-4b39-bbf7-71b4db751705
-- title:
--   Base case of the local comparison
-- statement:
--   Let $A$ be a domain, $S$ a local domain with residue map $\mathrm{res}$, $\varphi:A\to S$ a ring homomorphism, $p\in\mathbb N$ with $p$ prime in $A$, and $\varepsilon$ the augmentation of the group algebra $A[\mathbb Z/n]$. Say $x\sim y$ if $x=wy$ for a unit $w$ of $S$ with $\mathrm{res}(w)=1$. Let $v:A[\mathbb Z/n]\to S$ be a ring homomorphism with $v(a)=\varphi(a)$ on scalars and $\mathrm{res}(v(F))=\mathrm{res}(\varphi(\varepsilon(F)))$ for all $F$, and assume $\varphi(p)\ne0$. If $F,K\in A[\mathbb Z/n]$ and a unit $b$ of $A$ satisfy
--   $$
--   FK=p\,b,
--   $$
--   then $v(F)\sim\varphi(\varepsilon(F))$ and $v(K)\sim\varphi(\varepsilon(K))$.
--
--   When the norm has valuation one, each factor's value agrees with its augmentation up to a unit of residue one.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/LocalComparisonInduction.lean#L56-L88

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

theorem OAI.CirculantHadamard.LocalComparison.comparison_base (n p : ℕ) (φ : A →+* S) (hp : Prime (p : A))
    (hpS : φ (p : A) ≠ 0)
    (v : Elem A n →+* S)
    (vscalar : ∀ a : A, v (scalar n a) = φ a)
    (vres : ∀ F : Elem A n,
      IsLocalRing.residue S (v F) =
        IsLocalRing.residue S (φ (augmentation n F)))
    (b : Aˣ) (F K : Elem A n)
    (hFK : F * K = scalar n ((p : A) * (b : A))) :
    ResidueOneAssociated (IsLocalRing.residue S) (v F) (φ (augmentation n F)) ∧
      ResidueOneAssociated (IsLocalRing.residue S) (v K) (φ (augmentation n K)) := by sorry
