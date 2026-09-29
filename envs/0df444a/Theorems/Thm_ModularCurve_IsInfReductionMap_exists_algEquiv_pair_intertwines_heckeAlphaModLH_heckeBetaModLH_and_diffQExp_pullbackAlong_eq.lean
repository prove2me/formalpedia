-- Prove2me | Theorems.Thm_ModularCurve_IsInfReductionMap_exists_algEquiv_pair_intertwines_heckeAlphaModLH_heckeBetaModLH_and_diffQExp_pullbackAlong_eq
-- name    : ModularCurve.IsInfReductionMap.exists_algEquiv_pair_intertwines_heckeAlphaModLH_heckeBetaModLH_and_diffQExp_pullbackAlong_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/79f5554e-c37d-5ce3-a790-036956845bc8
-- title:
--   Fricke involution pair exchanging the mod p degeneracy maps
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $p \mid M$ and $p^2 \nmid M$, let $H \le (\mathbb{Z}/M)^\times$ contain every unit that maps to $1$ under the reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$, and assume $M/p \ne 0$. Let $K$ be an algebraically closed field of characteristic $p$, regarded as a $\mathbb{Z}/p$-algebra. Write $H' =$ [`ModularCurve.infSubgroup p M H hpM`](def/ModularCurve_XHDifferentialsModL.html#L246) for the image of $H$ in $(\mathbb{Z}/(M/p))^\times$, $\Gamma_{H'}$ for the corresponding subgroup of $\mathrm{SL}_2(\mathbb{Z})$ (the image of the preimage of $H'$ under $\Gamma_0(M/p) \to (\mathbb{Z}/(M/p))^\times$), and $F =$ [`ModularCurve.qExpFunctionFieldC K Γ`](def/ModularCurve_X1.html#L101) for the subfield of $\mathrm{LaurentSeries}\,K$ generated over $K$ by the quotients of reductions of integral $q$-expansions of equal-weight modular forms on $\Gamma$. Let $\rho_\infty : K \otimes_{\mathbb{Z}/p} \mathrm{IntTwoCuspForms}(M,H,p) \to \Omega_{F_{H'}/K}$ be $K$-linear and satisfy [`ModularCurve.IsInfReductionMap`](def/ModularCurve_XHDifferentialsModL.html#L443): for every weight-two cusp form $f$ on $\Gamma_H(M)$ lying in the two-cusp integral set over $\mathbb{Z} \subset \mathbb{C}$ (all $q$-coefficients of $tf$ and of $(tf)$ slashed by any Atkin–Lehner datum at $(M,p)$ are rational integers, for $t$ in the Hecke ring) and every integral power series $p_f$ with $q$-expansion equal to that of $f$, the value $\mathrm{diffQExp}(\rho_\infty(1 \otimes \bar f))$, for the derivation $q\,d/dq$, is the reduction of $p_f$ to $\mathrm{LaurentSeries}\,K$. Let $W_d$ be an Atkin–Lehner datum for $(M, M/p)$, let $e \in (\mathbb{Z}/M)^\times$ have image $\bar e$ in $\mathbb{Z}/(M/p)$ with $\bar e \cdot \bar p = 1$, let $\varphi$ be a ring homomorphism from the ring of algebraic integers in $\mathbb{C}$ to $K$ with $\varphi(p) = 0$, and let $q$ be a prime dividing $M/p$. Then there are a $K$-algebra automorphism $\sigma$ of $F_{H'} =$ `qExpFunctionFieldC K (CohCarrier.GammaH (M/p) H')` and a $K$-algebra automorphism $\tau$ of the function field of the roof level $\Gamma_{H'} \cap \Gamma_0((M/p)q)$ such that, with $\alpha =$ `heckeAlphaModLH` (the inclusion of the two fields) and $\beta =$ `heckeBetaModLH` (substitution $q \mapsto q^{q}$ when that lands in the roof field, and $\alpha$ otherwise), one has $\tau \circ \alpha = \beta \circ \sigma$, $\tau \circ \beta = \alpha \circ \sigma$ and $\sigma \circ \sigma = \mathrm{id}$, both $\alpha$ and $\beta$ are separable, and for every $f$ in the two-cusp integral set at level $(M,H)$, every natural number $D$ with $p \nmid D$, and every power series $p_{f,W}$ over the algebraic integers whose image in $\mathbb{C}[[q]]$ is the $q$-expansion of $D \cdot \big(\langle e\rangle f\big)\big|_2 W_d$, the identity $D \cdot \mathrm{diffQExp}\big(\sigma^{*}\rho_\infty(1 \otimes \bar f)\big) = \varphi(p_{f,W})$ holds in $\mathrm{LaurentSeries}\,K$, where $\sigma^{*}$ is the pullback of differentials along $\sigma$.
--
--   This packages the Fricke involutions $w_Q$ and $w_{Qq}$, for $Q = M/p$, as automorphisms of the characteristic-$p$ $q$-expansion function fields which interchange the two degeneracy legs of the $q$-correspondence, together with the effect of $\sigma$ on the $\infty$-component reduction of an integral weight-two cusp form. It feeds the construction of the $q$-correspondence on differentials used in the level-lowering step at a prime exactly dividing the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IsInfReductionMap_exists_algEquiv_pair_intertwines_heckeAlphaModLH_heckeBetaModLH_and_diffQExp_pullbackAlong_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups ModularForm

theorem ModularCurve.IsInfReductionMap.exists_algEquiv_pair_intertwines_heckeAlphaModLH_heckeBetaModLH_and_diffQExp_pullbackAlong_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p] [Algebra (ZMod p) K]
    (ρinf : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p →ₗ[K] Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K])
    (hρinf : ModularCurve.IsInfReductionMap K p M H hpM ρinf)
    (Wd : ModularForm.AtkinLehnerDatum M (M / p))
    (e : (ZMod M)ˣ) (he : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1)
    (φ : ↥(integralClosure ℤ ℂ) →+* K) (hφ : φ (p : ↥(integralClosure ℤ ℂ)) = 0)
    (q : ℕ) (hq : q.Prime) (hqQ : q ∣ M / p) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    ∃ (σ : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) ≃ₐ[K]
            ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))))
      (τ : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) ⊓ CongruenceSubgroup.Gamma0 (M / p * q))) ≃ₐ[K]
            ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) ⊓ CongruenceSubgroup.Gamma0 (M / p * q)))),

      (∀ x, τ (ModularCurve.heckeAlphaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) q x) =
          ModularCurve.heckeBetaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) q (σ x)) ∧

      (∀ x, τ (ModularCurve.heckeBetaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) q x) =
          ModularCurve.heckeAlphaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) q (σ x)) ∧

      (∀ x, σ (σ x) = x) ∧

      AlgebraicCurve.SeparableAlong K (ModularCurve.heckeAlphaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) q) ∧
      AlgebraicCurve.SeparableAlong K (ModularCurve.heckeBetaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) q) ∧

      (∀ (f : CuspForm (CohCarrier.GammaH M H) 2)
          (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
          (D : ℕ) (_ : ¬ p ∣ D)
          (pfW : PowerSeries ↥(integralClosure ℤ ℂ)),
          pfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
            UpperHalfPlane.qExpansion 1 ((D : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f)) →
          (D : K) • ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
              (AlgebraicCurve.Differential.pullbackAlong
                σ.toAlgHom
                (ρinf ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
                  ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩))) =
            HahnSeries.ofPowerSeries ℤ K (pfW.map φ)) := by sorry
