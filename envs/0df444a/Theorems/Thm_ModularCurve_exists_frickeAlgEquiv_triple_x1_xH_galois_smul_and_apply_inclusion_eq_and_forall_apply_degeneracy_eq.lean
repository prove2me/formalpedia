-- Prove2me | Theorems.Thm_ModularCurve_exists_frickeAlgEquiv_triple_x1_xH_galois_smul_and_apply_inclusion_eq_and_forall_apply_degeneracy_eq
-- name    : ModularCurve.exists_frickeAlgEquiv_triple_x1_xH_galois_smul_and_apply_inclusion_eq_and_forall_apply_degeneracy_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/01855904-ab40-5567-9bc1-2f329e7d76de
-- title:
--   Compatible Fricke involutions on X₁(M), X_H(M) and X_{H'}(M/p)
-- statement:
--   Setting. Let $p$ be a prime and $M$ a nonzero natural number with $p \mid M$ (hypothesis `hpM`) and $p^2 \nmid M$ (hypothesis `hpM2`), and let $H$ be a subgroup of $(\mathbb{Z}/M)^\times$ subject to the hypothesis `hHp`: every unit $u$ of $\mathbb{Z}/M$ whose image under `ZMod.unitsMap` for the divisibility $(M/p) \mid M$ is $1$ lies in $H$; the quotient $M/p$ is also nonzero. Write $H' =$ `infSubgroup p M H hpM` for the image of $H$ in $(\mathbb{Z}/(M/p))^\times$ under that same reduction of units.
--
--   The fields involved are subfields of the Laurent series field over $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`: `x1FunctionFieldBar M` is `laurentBaseChange` of the rational $q$-expansion function field `x1FunctionField M` of $X_1(M)$, i.e. the subfield of $\overline{\mathbb{Q}}$-Laurent series generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of that rational field, and likewise `xHFunctionFieldBar M H` for level $\Gamma_H(M)$ and `xHFunctionFieldBar (M / p) H'` for level $\Gamma_{H'}(M/p)$. The groups `JOne M` and `JH M H` are the corresponding $\mathrm{Pic}^0$ groups over $\overline{\mathbb{Q}}$, namely degree-zero divisors (finitely supported $\mathbb{Z}$-combinations of places, a place being a proper valuation subring of the field containing $\overline{\mathbb{Q}}$ which is a principal ideal ring) modulo principal divisors. A $\overline{\mathbb{Q}}$-algebra automorphism of such a field acts on $\mathrm{Pic}^0$ through `SemilinearAut.ofAlgAut`, the pair consisting of the automorphism together with the identity of $\overline{\mathbb{Q}}$; elements $\sigma$ of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ act through the semilinear automorphisms given by coefficientwise application of $\sigma$.
--
--   Finally, $\iota$ is a $\overline{\mathbb{Q}}$-algebra homomorphism from `xHFunctionFieldBar M H` to `x1FunctionFieldBar M` which, by hypothesis `hι`, is the identity on the underlying Laurent series.
--
--   Conclusion. There exist $\overline{\mathbb{Q}}$-algebra automorphisms $w_1$ of `x1FunctionFieldBar M`, $w$ of `xHFunctionFieldBar M H` and $w'$ of `xHFunctionFieldBar (M / p) H'` satisfying the following five groups of assertions.
--
--   (1) Four laws for $w_1$ on `JOne M`. (1a) For every prime $\ell$, given the Hecke input data at level $M$ (summarised here): integrality of the ring homomorphisms underlying `heckeAlphaOneBar` and `heckeBetaOneBar` from `laurentBaseChange` of `x1FunctionField M` to `laurentBaseChange` of `x1x0FunctionFieldC ℚ M (M * ℓ)` — the first being the inclusion, the second being the map induced by $q \mapsto q^{\ell}$ when `qExpand ℚ ℓ` carries `x1FunctionField M` into `x1x0FunctionFieldC ℚ M (M * ℓ)` and the inclusion otherwise — a `HasPrincipalDivisors` instance for the base-changed upper field, `FundamentalIdentityAlong` for each of the two maps, `FiniteAlong` for each of them, and `NormFormulaAlong` (the pushforward norm formula) for each of them: for all $x$ in `JOne M`,
--   $$\mathrm{heckePic0OneBarTranspose}(w_1 \cdot x) = w_1 \cdot \mathrm{heckePic0OneBar}(x),$$
--   where `heckePic0OneBar` is the correspondence obtained by pulling back along $\beta$ and pushing forward along $\alpha$, and `heckePic0OneBarTranspose` the one obtained by pulling back along $\alpha$ and pushing forward along $\beta$. (1b) For every natural number $d$ and every $x$ in `JOne M`, $\langle d\rangle (w_1 \cdot \langle d\rangle x) = w_1 \cdot x$, with $\langle d \rangle =$ `diamondOneBar M d`. (1c) $w_1 \cdot (w_1 \cdot x) = x$ for all $x$ in `JOne M`. (1d) For every $\sigma$ in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ and every natural number $c$ coprime to $M$ such that $\sigma\zeta = \zeta^{c}$ for all $\zeta$ with $\zeta^{M} = 1$, and all $x$ in `JOne M`,
--   $$w_1 \cdot (\sigma \cdot x) = \sigma \cdot \big(\mathrm{diamondOneBar}\,M\,c\,(w_1 \cdot x)\big).$$
--
--   (2) The same four laws for $w$ on `JH M H`, with the level-$\Gamma_H(M)$ Hecke data: for every prime $\ell$, integrality of `heckeAlphaHBar` and `heckeBetaHBar` (from `laurentBaseChange` of `xHFunctionField M H` to `laurentBaseChange` of `xHTopFunctionFieldC ℚ M H (M * ℓ)`, the inclusion and the $q \mapsto q^{\ell}$ map respectively, the latter replaced by the inclusion when it is not defined), a `HasPrincipalDivisors` instance for the base-changed upper field, and `FundamentalIdentityAlong`, `FiniteAlong`, `NormFormulaAlong` for both maps, one has `heckePic0HBarTranspose` applied to $w \cdot x$ equal to $w$ applied to `heckePic0HBar` of $x$; for every $d$ in $(\mathbb{Z}/M)^\times$ and $x$ in `JH M H`, $\mathrm{diamondHBar}\,M\,H\,d\,(w \cdot \mathrm{diamondHBar}\,M\,H\,d\,x) = w \cdot x$; $w \cdot (w \cdot x) = x$; and for $\sigma$, $c$ coprime to $M$ with $\sigma\zeta = \zeta^{c}$ on $M$-th roots of unity, $w \cdot (\sigma \cdot x) = \sigma \cdot \big(\mathrm{diamondHBar}\,M\,H\,(\mathrm{ZMod.unitOfCoprime}\,c\,hc)\,(w \cdot x)\big)$.
--
--   (3) The same four laws for $w'$ on `JH (M / p) H'`, with all data taken at level $\Gamma_{H'}(M/p)$: the Hecke maps `heckeAlphaHBar` and `heckeBetaHBar` for $(M/p, H', \ell)$ into `laurentBaseChange` of `xHTopFunctionFieldC ℚ (M / p) H' (M / p * ℓ)`, with the corresponding integrality, `HasPrincipalDivisors`, `FundamentalIdentityAlong`, `FiniteAlong` and `NormFormulaAlong` hypotheses; diamond operators indexed by $d$ in $(\mathbb{Z}/(M/p))^\times$; involutivity; and the Galois law with $c$ coprime to $M/p$ and $\sigma\zeta = \zeta^{c}$ for all $\zeta$ with $\zeta^{M/p} = 1$.
--
--   (4) Restriction square: $\iota(w\,u) = w_1(\iota\,u)$ for all $u$ in `xHFunctionFieldBar M H`.
--
--   (5) Degeneracy exchange, quantified inside the existential. For all $\overline{\mathbb{Q}}$-algebra homomorphisms $\alpha_H, \beta_H$ from `xHFunctionFieldBar (M / p) H'` to `xHFunctionFieldBar M H` such that $\alpha_H$ is the identity on underlying Laurent series and $\beta_H$ acts on them as `qExpand (AlgebraicClosure ℚ) p`, that is $q \mapsto q^{p}$ (multiplication of Laurent exponents by $p$), and such that the ring homomorphisms underlying both are integral, both satisfy `FiniteAlong`, and both satisfy the associated `NormFormulaAlong`, the following four identities hold: $\alpha_H(w'\,u) = w(\beta_H\,u)$ and $\beta_H(w'\,u) = w(\alpha_H\,u)$ for all $u$ in `xHFunctionFieldBar (M / p) H'`; and, on divisor classes, for all $x$ in `JH M H`,
--   $$\mathrm{Pic0.pushforwardAlongHom}\,\beta_H\,(w \cdot x) = w' \cdot \mathrm{Pic0.pushforwardAlongHom}\,\alpha_H\,x, \qquad \mathrm{Pic0.pushforwardAlongHom}\,\alpha_H\,(w \cdot x) = w' \cdot \mathrm{Pic0.pushforwardAlongHom}\,\beta_H\,x,$$
--   the pushforward maps going from `JH M H` to `JH (M / p) H'`.
--
--   This is the simultaneous construction of the Fricke involutions at the three levels $\Gamma_1(M)$, $\Gamma_H(M)$ and $\Gamma_{H'}(M/p)$, in the $q$-expansion model of the function fields, together with their standard compatibilities: conjugation turns a Hecke correspondence into its transpose, conjugation by a diamond operator inverts the involution, the involution is an involution on divisor classes, it is semilinear for the Galois action up to a cyclotomic diamond twist, it is compatible with the inclusion of the level-$H$ field into the level-$1$ field, and it exchanges the two degeneracy maps from level $M/p$ to level $M$, both on function fields and on $\mathrm{Pic}^0$. Producing all three involutions in one statement is what makes the exchange and the restriction law available; they feed the construction of the Hecke-self-adjoint pairing on the Tate module of $J_1(M)$ used in the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_frickeAlgEquiv_triple_x1_xH_galois_smul_and_apply_inclusion_eq_and_forall_apply_degeneracy_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_ModularCurve_X1HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_frickeAlgEquiv_triple_x1_xH_galois_smul_and_apply_inclusion_eq_and_forall_apply_degeneracy_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]

    (ι : ↥(xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(x1FunctionFieldBar M))
    (hι : ∀ x : ↥(xHFunctionFieldBar M H), ((ι x : ↥(x1FunctionFieldBar M)) : LaurentSeries (AlgebraicClosure ℚ)) = (x : LaurentSeries (AlgebraicClosure ℚ))) :
    ∃ (w₁ : ↥(x1FunctionFieldBar M) ≃ₐ[AlgebraicClosure ℚ] ↥(x1FunctionFieldBar M))
      (w : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)) (w' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))),

      ((∀ (ℓ : ℕ) [Fact ℓ.Prime]
          (hα : HeckeAlphaOneBarIntegral (AlgebraicClosure ℚ) M ℓ)
          (hβ : HeckeBetaOneBarIntegral (AlgebraicClosure ℚ) M ℓ)
          [HasPrincipalDivisors (AlgebraicClosure ℚ)
            (laurentBaseChange (AlgebraicClosure ℚ) (x1x0FunctionFieldC ℚ M (M * ℓ)))]
          (hFIβ : FundamentalIdentityAlong (AlgebraicClosure ℚ)
            (heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ) hβ)
          (hfinα : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ))
          (hNα : NormFormulaAlong (AlgebraicClosure ℚ)
            (heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ) hfinα)
          (hFIα : FundamentalIdentityAlong (AlgebraicClosure ℚ)
            (heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ) hα)
          (hfinβ : FiniteAlong (AlgebraicClosure ℚ) (heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ))
          (hNβ : NormFormulaAlong (AlgebraicClosure ℚ)
            (heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ) hfinβ)
          (x : JOne M),
        heckePic0OneBarTranspose hα hβ hFIα hfinβ hNβ (SemilinearAut.ofAlgAut w₁ • x)
          = SemilinearAut.ofAlgAut w₁ • heckePic0OneBar hα hβ hFIβ hfinα hNα x) ∧
      (∀ (d : ℕ) (x : JOne M),
        diamondOneBar M d (SemilinearAut.ofAlgAut w₁ • diamondOneBar M d x)
          = SemilinearAut.ofAlgAut w₁ • x) ∧
      (∀ x : JOne M, SemilinearAut.ofAlgAut w₁ • (SemilinearAut.ofAlgAut w₁ • x) = x) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ), c.Coprime M →
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) → ∀ x : JOne M,
          SemilinearAut.ofAlgAut w₁ • (σ • x)
            = σ • diamondOneBar M c (SemilinearAut.ofAlgAut w₁ • x))) ∧

      ((∀ (ℓ : ℕ) [Fact ℓ.Prime]
          (hα : HeckeAlphaHBarIntegral (AlgebraicClosure ℚ) M H ℓ)
          (hβ : HeckeBetaHBarIntegral (AlgebraicClosure ℚ) M H ℓ)
          [HasPrincipalDivisors (AlgebraicClosure ℚ)
            (laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ M H (M * ℓ)))]
          (hFIβ : FundamentalIdentityAlong (AlgebraicClosure ℚ)
            (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ) hβ)
          (hfinα : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ))
          (hNα : NormFormulaAlong (AlgebraicClosure ℚ)
            (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ) hfinα)
          (hFIα : FundamentalIdentityAlong (AlgebraicClosure ℚ)
            (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ) hα)
          (hfinβ : FiniteAlong (AlgebraicClosure ℚ) (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ))
          (hNβ : NormFormulaAlong (AlgebraicClosure ℚ)
            (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ) hfinβ)
          (x : JH M H),
        heckePic0HBarTranspose hα hβ hFIα hfinβ hNβ (SemilinearAut.ofAlgAut w • x)
          = SemilinearAut.ofAlgAut w • heckePic0HBar hα hβ hFIβ hfinα hNα x) ∧
      (∀ (d : (ZMod M)ˣ) (x : JH M H),
        diamondHBar M H d (SemilinearAut.ofAlgAut w • diamondHBar M H d x)
          = SemilinearAut.ofAlgAut w • x) ∧
      (∀ x : JH M H, SemilinearAut.ofAlgAut w • (SemilinearAut.ofAlgAut w • x) = x) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ) (hc : c.Coprime M),
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) →
          ∀ x : JH M H,
            SemilinearAut.ofAlgAut w • (σ • x)
              = σ • diamondHBar M H (ZMod.unitOfCoprime c hc) (SemilinearAut.ofAlgAut w • x))) ∧
      ((∀ (ℓ : ℕ) [Fact ℓ.Prime]
          (hα : HeckeAlphaHBarIntegral (AlgebraicClosure ℚ) (M / p) (infSubgroup p M H hpM) ℓ)
          (hβ : HeckeBetaHBarIntegral (AlgebraicClosure ℚ) (M / p) (infSubgroup p M H hpM) ℓ)
          [HasPrincipalDivisors (AlgebraicClosure ℚ)
            (laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ (M / p) (infSubgroup p M H hpM) (M / p * ℓ)))]
          (hFIβ : FundamentalIdentityAlong (AlgebraicClosure ℚ)
            (heckeBetaHBar (AlgebraicClosure ℚ) (M / p) (infSubgroup p M H hpM) ℓ) hβ)
          (hfinα : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaHBar (AlgebraicClosure ℚ) (M / p) (infSubgroup p M H hpM) ℓ))
          (hNα : NormFormulaAlong (AlgebraicClosure ℚ)
            (heckeAlphaHBar (AlgebraicClosure ℚ) (M / p) (infSubgroup p M H hpM) ℓ) hfinα)
          (hFIα : FundamentalIdentityAlong (AlgebraicClosure ℚ)
            (heckeAlphaHBar (AlgebraicClosure ℚ) (M / p) (infSubgroup p M H hpM) ℓ) hα)
          (hfinβ : FiniteAlong (AlgebraicClosure ℚ) (heckeBetaHBar (AlgebraicClosure ℚ) (M / p) (infSubgroup p M H hpM) ℓ))
          (hNβ : NormFormulaAlong (AlgebraicClosure ℚ)
            (heckeBetaHBar (AlgebraicClosure ℚ) (M / p) (infSubgroup p M H hpM) ℓ) hfinβ)
          (x : JH (M / p) (infSubgroup p M H hpM)),
        heckePic0HBarTranspose hα hβ hFIα hfinβ hNβ (SemilinearAut.ofAlgAut w' • x)
          = SemilinearAut.ofAlgAut w' • heckePic0HBar hα hβ hFIβ hfinα hNα x) ∧
      (∀ (d : (ZMod (M / p))ˣ) (x : JH (M / p) (infSubgroup p M H hpM)),
        diamondHBar (M / p) (infSubgroup p M H hpM) d (SemilinearAut.ofAlgAut w' • diamondHBar (M / p) (infSubgroup p M H hpM) d x)
          = SemilinearAut.ofAlgAut w' • x) ∧
      (∀ x : JH (M / p) (infSubgroup p M H hpM), SemilinearAut.ofAlgAut w' • (SemilinearAut.ofAlgAut w' • x) = x) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ) (hc : c.Coprime (M / p)),
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ (M / p) = 1 → σ ζ = ζ ^ c) →
          ∀ x : JH (M / p) (infSubgroup p M H hpM),
            SemilinearAut.ofAlgAut w' • (σ • x)
              = σ • diamondHBar (M / p) (infSubgroup p M H hpM) (ZMod.unitOfCoprime c hc) (SemilinearAut.ofAlgAut w' • x))) ∧

      (∀ u : ↥(xHFunctionFieldBar M H), ι (w u) = w₁ (ι u)) ∧

      (∀ (αH βH : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
          (hα : ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), ((αH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
          (hβ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
            ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), ((βH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
          (hαint : αH.toRingHom.IsIntegral) (hβint : βH.toRingHom.IsIntegral)
          (hαfin : FiniteAlong (AlgebraicClosure ℚ) αH) (hβfin : FiniteAlong (AlgebraicClosure ℚ) βH)
          (hαN : NormFormulaAlong (AlgebraicClosure ℚ) αH hαfin) (hβN : NormFormulaAlong (AlgebraicClosure ℚ) βH hβfin),
        (∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), αH (w' u) = w (βH u)) ∧
          (∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), βH (w' u) = w (αH u)) ∧

          (∀ x : JH M H,
        Pic0.pushforwardAlongHom βH hβint hβfin hβN (SemilinearAut.ofAlgAut w • x)
          = SemilinearAut.ofAlgAut w' • Pic0.pushforwardAlongHom αH hαint hαfin hαN x) ∧
          (∀ x : JH M H,
        Pic0.pushforwardAlongHom αH hαint hαfin hαN (SemilinearAut.ofAlgAut w • x)
          = SemilinearAut.ofAlgAut w' • Pic0.pushforwardAlongHom βH hβint hβfin hβN x)) := by sorry
