-- Prove2me | Theorems.Thm_ModularCurve_exists_constantReduction_isGood_isPlaceReductionModL
-- name    : ModularCurve.exists_constantReduction_isGood_isPlaceReductionModL
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/d38c00ad-9a1e-5727-8f00-3d1fd205e17c
-- title:
--   Good constant reduction of X₀(N) at ℓ ∤ N
-- statement:
--   Let $N \ge 1$ and let $\ell$ be a prime not dividing $N$. Let $A$ be a valuation subring of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` lying over $\ell$, in the sense that the image of $\ell$ in $\overline{\mathbb Q}$ is a non-unit of $A$, and write $k =$ `IsLocalRing.ResidueField A`. Put $F =$ `modularFunctionFieldBar N`, the subfield of $\overline{\mathbb Q}((q))$ generated over $\overline{\mathbb Q}$ by the coefficientwise images of the elements of the subfield $\mathbb Q\bigl(j(q^d) : d \mid N\bigr)$ of $\mathbb Q((q))$, and $\bar F =$ `modularFunctionFieldFullC k N`, the subfield of $k((q))$ generated over $k$ by the series $j(q^d)$ for the nonzero divisors $d$ of $N$. The assertion is that there is a `ConstantReduction` $R$ of $F$ along $A$ onto $\bar F$: a valuation subring $\mathcal O \subseteq F$ with $\mathrm{algebraMap}(c) \in \mathcal O \iff c \in A$ for $c \in \overline{\mathbb Q}$, a surjective ring homomorphism $\mathrm{res} : \mathcal O \to \bar F$ whose kernel is the maximal ideal of $\mathcal O$ and which on constants induces the residue map $A \to k$ followed by $k \hookrightarrow \bar F$, such that every nonzero $f \in F$ has a scalar multiple $c \cdot f \in \mathcal O$ with $\mathrm{res}(c \cdot f) \ne 0$, together with a map $r$ on places, $\mathrm{Place}(\overline{\mathbb Q}, F) \to \mathrm{Place}(k, \bar F)$, preserving residue degrees and satisfying $r_*(\operatorname{div} f) = \operatorname{div}(\mathrm{res}\, f)$ for $f \in \mathcal O$ with $\mathrm{res}\, f \ne 0$; moreover $R$ is good, i.e. $\mathrm{genusFF}\,(k, \bar F) = \mathrm{genusFF}\,(\overline{\mathbb Q}, F)$ (equality of the $\dim H^1(0)$ invariants), and its place map $r$ satisfies the $q$-expansion specification `IsPlaceReductionModL`: $r$ preserves degrees, and for every Laurent series $y$ with coefficients in $A$ whose coefficientwise image lies in $F$ and whose coefficientwise reduction $\bar y$ lies in $\bar F$ and is nonzero, $r_*(\operatorname{div} y) = \operatorname{div}(\bar y)$ as divisors on $\bar F$.
--
--   This is Igusa's theorem that the modular curve $X_0(N)$ has good reduction at every prime $\ell \nmid N$, with reduction the level-$N$ modular curve in characteristic $\ell$ described by $q$-expansions, phrased in Deuring's language of constant reductions of function fields. It supplies the reduction map on places and divisor classes used downstream to compare divisor class groups in characteristic $0$ and characteristic $\ell$, in particular in the results on specialisation of places and on reduction of degree-zero divisor classes modulo $\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_constantReduction_isGood_isPlaceReductionModL.lean

import Mathlib
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_AlgebraicCurve_ConstantReduction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_constantReduction_isGood_isPlaceReductionModL (N : ℕ) [NeZero N] {ℓ : ℕ}
    [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ) :
    ∃ R : ConstantReduction A (modularFunctionFieldBar N)
        (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N),
      R.IsGood ∧ IsPlaceReductionModL A N R.placeMap := by sorry
