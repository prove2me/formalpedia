-- Prove2me | Theorems.Thm_ModularCurve_CharPModel_FibreModel_reductionModL_eq_pic0Congr_spPic0
-- name    : ModularCurve.CharPModel.FibreModel.reductionModL_eq_pic0Congr_spPic0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/6ee2c43b-79dd-5cfe-baf1-7ed64ab41b5e
-- title:
--   Reduction mod ℓ on J₀(N) equals the constructed specialisation
-- statement:
--   Fix $N \ge 1$ and a prime $\ell$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ whose residue field $\kappa = \mathrm{ResidueField}(A)$ has characteristic $\ell$, with $\ell \nmid N$. Let `fm` be a `FibreModel` for $N$, $A$, $\ell$ over $\kappa$ with respect to the residue map $A \to \kappa$, i.e. a pair of subrings $B_{\mathrm{Fin}}, B_{\mathrm{Inf}}$ of the base change to $\overline{\mathbb{Q}}$ of the full modular function field, containing the constants from $A$ and containing $\bar\jmath, \bar\jmath_N$ respectively $\bar\jmath^{-1}$, integral over the respective affine bases, together with homomorphisms $\pi_{\mathrm{Fin}}, \pi_{\mathrm{Inf}}$ to $\mathrm{modularFunctionFieldC}\,\kappa\,N = \kappa(j(q), j(q^N))$ reducing constants via the residue map and sending $\bar\jmath, \bar\jmath_N, \bar\jmath^{-1}$ to the corresponding mod-$\ell$ $q$-expansions; let `cc` be a cusp chart for `fm`, asserting $\bar\jmath_N\bar\jmath^{-N} \in B_{\mathrm{Inf}}$ with the expected image under $\pi_{\mathrm{Inf}}$. Let `dataAll` assign to each divisor $d \mid N$ modular polynomial data (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(d)$ vanishing at $(j, j_{d})$), let `hsep` assert that $\Phi_N$ reduced mod $\ell$ is separable over $\kappa(X)$, let `h` be the predicate `ReductionInputsModL` for $A$ and $N$, let `hCF` be the equality of intermediate fields $\mathrm{modularFunctionFieldC}\,\kappa\,N = \mathrm{modularFunctionFieldFullC}\,\kappa\,N$, and let `hpres` assert that the divisor-level specialisation `fm.spDiv` carries degree-zero divisors of $\mathrm{modularFunctionFieldBar}\,N$ over $\overline{\mathbb{Q}}$ to degree-zero divisors, and principal ones among these to principal divisors, of $\kappa(j(q), j(q^N))$ over $\kappa$. Then for every $x \in \mathrm{JZero}\,N = \mathrm{Pic}^0(\overline{\mathbb{Q}}, \mathrm{modularFunctionFieldBar}\,N)$ one has $\mathrm{reductionModL}\,A\,N\,x = \iota(\mathrm{spPic0}(x))$, where $\mathrm{spPic0}$ is the map on degree-zero classes induced by `fm.spDiv` (well defined by `hpres`) and $\iota$ is the isomorphism of degree-zero class groups induced by the field equality `hCF`.
--
--   This identifies the canonical reduction map on divisor classes of $J_0(N)$ at a place above $\ell$, in the style of Deuring's reduction theory, with the specialisation map built from an explicit fibre model, once the two descriptions of the special-fibre function field are identified. It is the bridge used by the statements about the finite flat model and the Eisenstein quotient and by the compatibility of Hecke operators with the specialisation map on $\mathrm{Pic}^0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CharPModel_FibreModel_reductionModL_eq_pic0Congr_spPic0.lean

import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_Pic0Congr

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve ModularCurve.CharPModel IsLocalRing
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in

theorem ModularCurve.CharPModel.FibreModel.reductionModL_eq_pic0Congr_spPic0
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (IsLocalRing.ResidueField A) ℓ]
    (hℓN : ¬ ℓ ∣ N)
    (fm : ModularCurve.CharPModel.FibreModel N A ℓ (IsLocalRing.ResidueField A)
      (IsLocalRing.residue A))
    (cc : fm.CuspChart)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularCurve.ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom (IsLocalRing.ResidueField A)))).map
      (algebraMap (Polynomial (IsLocalRing.ResidueField A)) (RatFunc (IsLocalRing.ResidueField A)))).Separable)
    (h : ModularCurve.ReductionInputsModL A N)
    (hCF : modularFunctionFieldC (IsLocalRing.ResidueField A) N =
      modularFunctionFieldFullC (IsLocalRing.ResidueField A) N)
    (hpres : fm.SpDivPreservesPrincipal Ideal.Quotient.mk_surjective dataAll hsep) :
    ∀ x : ModularCurve.JZero N,
      ModularCurve.reductionModL A N x =
        AlgebraicCurve.Pic0.congr
          (IntermediateField.equivOfEq hCF).toRingEquiv
          (fun a => (IntermediateField.equivOfEq hCF).commutes a)
          (fm.spPic0 Ideal.Quotient.mk_surjective dataAll hsep x) := by sorry
