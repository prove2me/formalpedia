-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_spPic0_eq_reductionModL
-- name    : ModularCurve.PlaceSpecialization.spPic0_eq_reductionModL
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/d5327004-d05c-5584-b43f-ae7b448b64ec
-- title:
--   Specialization on Pic⁰ agrees with reduction mod ℓ
-- statement:
--   Fix a natural number $N \neq 0$ and a prime $\ell$ with $\ell \nmid N$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $\ell$, meaning that the image of $\ell$ is a nonunit of $A$, and assume that the residue field $k = \mathrm{ResidueField}\,A$ has characteristic $\ell$ and is algebraically closed. Let `data` be modular polynomial data for $\ell$, i.e. a monic polynomial $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(\ell)$ annihilating the pair $(j, j_\ell)$ of $q$-expansions, and let `hKr` assert the Kronecker congruence, that the reduction of $\Phi$ modulo $\ell$ equals $(C X^\ell - X)(C X - X^\ell)$; let `hα` and `hβ` assert that the ring homomorphisms $\bar\alpha$ and $\bar\beta$ attached to level $N$ and $\ell$ over $\overline{\mathbb{Q}}$ are integral. Let $S$ be a place specialization for these data with residue target $k$ and reduction map the residue homomorphism $A \to k$; among its components are a map $\mathrm{sp}$ from places of $\overline{\mathbb{Q}}$-function field $\mathrm{modularFunctionFieldBar}\,N$ to places of $\mathrm{modularFunctionFieldC}\,k\,N$ and an additive homomorphism $S.\mathrm{spPic0}$ from $J_0(N) = \mathrm{Pic}^0$ of the former to $\mathrm{Pic}^0$ of the latter. The assertion is that for every class $x \in J_0(N)$ one has $S.\mathrm{spPic0}\,x = \tau^{-1}(\mathrm{reductionModL}\,A\,N\,x)$, where $\tau$ is the isomorphism of degree-zero class groups `Pic0.congr` induced by the equality of intermediate fields $\mathrm{modularFunctionFieldC}\,k\,N = \mathrm{modularFunctionFieldFullC}\,k\,N$ (valid since $\ell \nmid N$), together with its compatibility with the constants $k$.
--
--   This identifies the $\mathrm{Pic}^0$-component of the place specialization of $X_0(N)$ at a place of $\overline{\mathbb{Q}}$ above $\ell \nmid N$ with the reduction of $J_0(N)$ modulo $\ell$ constructed from the chosen reduction data, the two being compared through the identification of the two function fields of the special fibre. It is used in the comparison of prime-to-$p$ torsion under specialization and in the compatibility of the specialization with the Hecke correspondence at primes other than $\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_spPic0_eq_reductionModL.lean

import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_AlgebraicCurve_Pic0Congr
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ValuationSubring AlgebraicCurve IsLocalRing
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

theorem ModularCurve.PlaceSpecialization.spPic0_eq_reductionModL
    (N : ℕ) [NeZero N]
    (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    [CharP (ResidueField ↥A) ℓ] [IsAlgClosed (ResidueField ↥A)]
    (S : PlaceSpecialization A ℓ N data hKr (ResidueField ↥A)
        (IsLocalRing.residue ↥A) hα hβ) :
    ∀ x : JZero N,
      S.spPic0 x =
        (Pic0.congr
          (IntermediateField.equivOfEq
            (ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC (ResidueField ↥A) ℓ N
              hℓN)).toRingEquiv
          (fun a => (IntermediateField.equivOfEq
            (ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC (ResidueField ↥A) ℓ N
              hℓN)).commutes a)).symm (reductionModL A N x) := by sorry
