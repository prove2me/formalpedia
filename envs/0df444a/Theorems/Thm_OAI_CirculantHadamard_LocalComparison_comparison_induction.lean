-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_LocalComparison_comparison_induction
-- name    : OAI.CirculantHadamard.LocalComparison.comparison_induction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:55:18.591018+00:00
-- url     : https://prove2.me/theorems/92c43765-a3e4-4919-b90d-9b2334899ee6
-- title:
--   The local comparison induction over p-power levels
-- statement:
--   Let $A$ be a domain, $S$ a local domain with residue map $\mathrm{res}$, $\varphi:A\to S$ a ring homomorphism, $p\in\mathbb N$ with $p$ prime in $A$, and $\varepsilon$ the augmentation of the group algebra $A[\mathbb Z/n]$. Say $x\sim y$ if $x=wy$ for a unit $w$ of $S$ with $\mathrm{res}(w)=1$. Assume $\varphi(p)\ne0$, and let $v_e:A[\mathbb Z/p^{e+1}]\to S$ be ring homomorphisms that agree with $\varphi$ on scalars, satisfy $v_e\circ\pi=v_{e+1}$ for the projections $\pi$, and at level $0$ satisfy $\mathrm{res}(v_0(F))=\mathrm{res}(\varphi(\varepsilon(F)))$. Assume that whenever $FK=p^{e+2}b$ at level $e+1$, the projection of $F$ or of $K$ is divisible by $p$. Then for all $e$, units $b$, and $F,K$ with
--   $$
--   FK=p^{e+1}\,b,
--   $$
--   we have $v_e(F)\sim\varphi(\varepsilon(F))$ and $v_e(K)\sim\varphi(\varepsilon(K))$.
--
--   So, given the divisibility input, the value of each factor of a $p$-power norm equals its augmentation up to a unit of residue one.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/LocalComparisonInduction.lean#L132-L171

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

theorem OAI.CirculantHadamard.LocalComparison.comparison_induction (p : ℕ) (φ : A →+* S)
    (hp : Prime (p : A)) (hpS : φ (p : A) ≠ 0)
    (v : (e : ℕ) → Elem A (p ^ (e + 1)) →+* S)
    (vscalar : ∀ e a, v e (scalar (p ^ (e + 1)) a) = φ a)
    (vres : ∀ F : Elem A (p ^ 1),
      IsLocalRing.residue S (v 0 F) =
        IsLocalRing.residue S (φ (augmentation (p ^ 1) F)))
    (vq : ∀ e F,
      v e (cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) F) = v (e + 1) F)
    (hdivide : ∀ e (b : Aˣ) (F K : Elem A (p ^ (e + 2))),
      F * K = scalar (p ^ (e + 2)) ((p : A) ^ (e + 2) * (b : A)) →
      (∃ F', cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) F =
        scalar (p ^ (e + 1)) (p : A) * F') ∨
      (∃ K', cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) K =
        scalar (p ^ (e + 1)) (p : A) * K')) :
    ∀ e (b : Aˣ) (F K : Elem A (p ^ (e + 1))),
      F * K = scalar (p ^ (e + 1)) ((p : A) ^ (e + 1) * (b : A)) →
      ResidueOneAssociated (IsLocalRing.residue S) (v e F)
        (φ (augmentation (p ^ (e + 1)) F)) ∧
      ResidueOneAssociated (IsLocalRing.residue S) (v e K)
        (φ (augmentation (p ^ (e + 1)) K)) := by sorry
