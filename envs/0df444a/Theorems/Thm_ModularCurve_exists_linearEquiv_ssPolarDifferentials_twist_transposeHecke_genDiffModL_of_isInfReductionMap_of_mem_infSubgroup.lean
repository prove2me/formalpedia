-- Prove2me | Theorems.Thm_ModularCurve_exists_linearEquiv_ssPolarDifferentials_twist_transposeHecke_genDiffModL_of_isInfReductionMap_of_mem_infSubgroup
-- name    : ModularCurve.exists_linearEquiv_ssPolarDifferentials_twist_transposeHecke_genDiffModL_of_isInfReductionMap_of_mem_infSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/1f78a2a2-07c7-51f0-a7c3-4117c79f65e4
-- title:
--   Atkin–Lehner twist intertwining transposed Hecke action on supersingular polar differentials
-- statement:
--   Fix a prime $p$ and a positive integer $M$, a subgroup $H \le (\mathbf{Z}/M)^{\times}$, and an algebraically closed field $K$ of characteristic $p$ (carrying a $\mathbf{Z}/p$-algebra structure), together with a set $S$ of natural numbers.
--
--   The level hypotheses are: $p \mid M$ (`hpM`), $p^{2} \nmid M$ (`hpM2`), and `hHp`, which requires that every unit $u \in (\mathbf{Z}/M)^{\times}$ whose image under `ZMod.unitsMap` to $(\mathbf{Z}/(M/p))^{\times}$ is $1$ already lies in $H$. Write $H' =$ [`ModularCurve.infSubgroup p M H hpM`](def/ModularCurve_XHDifferentialsModL.html#L246), the image of $H$ in $(\mathbf{Z}/(M/p))^{\times}$, and let $\Gamma' =$ [`CohCarrier.GammaH (M / p) H'`](def/CohCarrier_Level.html#L133) be the associated congruence subgroup of $\mathrm{SL}_2(\mathbf{Z})$, namely the preimage in $\Gamma_0(M/p)$ of $H'$ under the lower-right-entry character. The curve is realised through its $q$-expansion function field $F =$ [`ModularCurve.qExpFunctionFieldC K Γ'`](def/ModularCurve_X1.html#L101): the intermediate field of the Laurent series field $K((q))$ generated over $K$ by all quotients `intSeriesC K pf / intSeriesC K pg` of coefficientwise reductions to $K$ of integral power series $p_f, p_g$ realising the $q$-expansions of two modular forms of the same weight on $\Gamma'$ (with the denominator nonzero). All differentials below live in $\Omega[F/K]$.
--
--   The submodule [`ModularCurve.ssPolarDifferentials K Γ' p`](def/ModularCurve_XHDifferentialsModL.html#L35), abbreviated $\Omega^{\mathrm{ss}}$, consists of those $\omega \in \Omega[F/K]$ that are regular at every place of $F/K$ outside the supersingular locus `ssPlacesQExp K Γ' p` and have at most a simple pole at each place of that locus.
--
--   The reduction-map hypotheses concern a $K$-linear map
--   $$\rho^{\infty} : K \otimes_{\mathbf{Z}/p} \mathrm{IntTwoCuspForms}(M,H,p) \longrightarrow \Omega[F/K],$$
--   where [`CuspForm.IntTwoCuspForms M H p`](def/ModularCurve_XHDifferentialsModL.html#L374) is the quotient of the two-cusp integral lattice `twoCuspLattice M H 2 p ⊥` (the $\mathbf{Z}$-span inside weight-two cusp forms on `GammaH M H` of those $f$ all of whose Hecke translates $tf$, and all Atkin–Lehner slashes of such translates, have integral $q$-coefficients) by $p$ times that lattice. The hypothesis `hρinf` states that $\rho^{\infty}$ is an `IsInfReductionMap`: for every weight-two cusp form $f$ on `GammaH M H` lying in `twoCuspIntegralSet M H 2 p ⊥` and every integral power series $p_f$ whose image in $\mathbf{C}[[q]]$ is the $q$-expansion of $f$, the composite of $\rho^{\infty}(1 \otimes \bar f)$ with `diffQExp` (the $F$-linear map $\Omega[F/K] \to K((q))$ induced by the derivation $q\,d/dq$) equals `intSeriesC K pf`. The hypothesis `hrange` states that the range of $\rho^{\infty}$ is exactly $\Omega^{\mathrm{ss}}$.
--
--   The remaining data are: an Atkin–Lehner datum `Wd : ModularForm.AtkinLehnerDatum M (M / p)`, that is, an integer $R$ with $M = (M/p) \cdot R$ together with integers $a, b$ satisfying $(M/p)a - Rb = 1$; a unit $e \in (\mathbf{Z}/M)^{\times}$ whose image $\bar e$ in $\mathbf{Z}/(M/p)$ satisfies $\bar e \cdot \bar p = 1$ (`he`); and a unit $d \in (\mathbf{Z}/M)^{\times}$ whose image in $\mathbf{Z}/(M/p)$ equals $\bar p$ (`hd`) and such that the image of $d$ in $(\mathbf{Z}/(M/p))^{\times}$, or else its negative, lies in $H'$ (`hdH`).
--
--   Under these hypotheses there exists a $K$-linear automorphism $W$ of $\Omega^{\mathrm{ss}}$ satisfying the following six conditions.
--
--   First (normalisation on forms): for every weight-two cusp form $f$ on `GammaH M H` with $f \in$ `twoCuspIntegralSet M H 2 p ⊥`, every integral power series $p_{fW}$ whose complex image is the $q$-expansion of `alSlash Wd 2 (diamondLinH 2 e f)` — the weight-two slash by the Atkin–Lehner matrix of `Wd` of the diamond translate $\langle e \rangle f$ — and every $\omega \in \Omega^{\mathrm{ss}}$ with $\omega = \rho^{\infty}(1 \otimes \bar f)$, one has `diffQExp F (W ω) = intSeriesC K pfW`.
--
--   Second (Hecke operators away from the level): for every prime $\ell$ with $\ell \notin S$ and $\ell \nmid M$, and all $\omega, \omega' \in \Omega^{\mathrm{ss}}$, if $\omega'$ is the image of $\omega$ under [`AlgebraicCurve.Differential.correspondence (heckeAlphaModLH K (M/p) H' ℓ) (heckeBetaModLH K (M/p) H' ℓ)`](def/AlgebraicCurve_DifferentialPushPull.html#L69), i.e. pullback along `heckeBetaModLH` followed by the trace along `heckeAlphaModLH` (here `heckeAlphaModLH` is the inclusion of $F$ into the $q$-expansion function field of $\Gamma' \cap \Gamma_0((M/p)\ell)$ and `heckeBetaModLH` is the map induced by $q \mapsto q^{\ell}$ when that map lands in the larger field, and the inclusion otherwise), then $W\omega' =$ `genDiffModL K p M H hpM S (CohCarrier.Gen.T ℓ _ _ _) (W ω)`, which on the generator $T_\ell$ is `heckeDiffModLH K (M/p) H' ℓ`, the correspondence taken in the opposite order, pullback along `heckeAlphaModLH` followed by the trace along `heckeBetaModLH`.
--
--   Third (Hecke operators at primes dividing the level other than $p$): for every prime $q'$ with $q' \mid M$ and $q' \neq p$, and all $\omega, \omega' \in \Omega^{\mathrm{ss}}$, if $\omega'$ is the image of $\omega$ under `Differential.correspondence (heckeAlphaModLH K (M/p) H' q') (heckeBetaModLH K (M/p) H' q')`, then $W\omega' =$ `genDiffModL … (CohCarrier.Gen.U q' _ _) (W ω)`, which for $q' \neq p$ is again `heckeDiffModLH K (M/p) H' q'`.
--
--   Fourth (diamond operators): for every unit $d \in (\mathbf{Z}/M)^{\times}$ (the quantifier rebinds the name $d$) and all $\omega, \omega' \in \Omega^{\mathrm{ss}}$, if $\omega' =$ `genDiffModL … (CohCarrier.Gen.dia d⁻¹) ω`, then $W\omega' =$ `genDiffModL … (CohCarrier.Gen.dia d) (W ω)`; on a generator $\langle d \rangle$ the operator `genDiffModL` is `diamondDiffModLH K (M/p) H'` at the image of $d$ in $(\mathbf{Z}/(M/p))^{\times}$, the pullback along the diamond action of a lift of the inverse unit.
--
--   Fifth (the operator at $p$): for all $\omega, \omega' \in \Omega^{\mathrm{ss}}$, if $\omega' =$ `genDiffModL … (CohCarrier.Gen.U p _ hpM) ω`, then $W\omega' =$ `genDiffModL … (CohCarrier.Gen.U p _ hpM) (W ω)`; on this generator `genDiffModL` is `frobPushDiffModL K Γ' p`, a linear map satisfying the predicate `IsFrobPushDiff` if one exists and $0$ otherwise. Thus $W$ commutes with the operator at $p$, rather than transposing it.
--
--   Sixth (regularity): for every $\omega \in \Omega^{\mathrm{ss}}$, the differential $\omega$ lies in [`AlgebraicCurve.regularDifferentials K F`](def/AlgebraicCurve_RegularDifferentials.html#L26) if and only if $W\omega$ does, where a differential is regular when at each place $v$ it is of the form $f \cdot dt_v$ with $f$ in the valuation subring of $v$ and $t_v$ a uniformiser.
--
--   This realises the Atkin–Lehner involution $w_{M/p}$ as an automorphism of the supersingular polar differentials of the modular curve for $\Gamma_{H'}(M/p)$ in characteristic $p$: it converts the transposed Hecke correspondences (trace along the degeneracy map composed after pullback along the $q \mapsto q^{\ell}$ map) into the covariant operators `genDiffModL`, fixes the operator at $p$, preserves regularity, and pins the image of a two-cusp integral form to the $q$-expansion of its $w_{M/p}$-translate twisted by $\langle e \rangle$. It is used in the construction of the $\mathrm{dlog}$ map from $p$-torsion of the Jacobian to supersingular polar differentials, in the level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_linearEquiv_ssPolarDifferentials_twist_transposeHecke_genDiffModL_of_isInfReductionMap_of_mem_infSubgroup.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

theorem ModularCurve.exists_linearEquiv_ssPolarDifferentials_twist_transposeHecke_genDiffModL_of_isInfReductionMap_of_mem_infSubgroup
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p] [Algebra (ZMod p) K] (S : Set ℕ)

    (ρinf : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p →ₗ[K] Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K])
    (hρinf : ModularCurve.IsInfReductionMap K p M H hpM ρinf)
    (hrange : LinearMap.range ρinf = ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)

    (Wd : ModularForm.AtkinLehnerDatum M (M / p))
    (e : (ZMod M)ˣ) (he : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1)

    (d : (ZMod M)ˣ) (hd : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (hdH : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ ModularCurve.infSubgroup p M H hpM ∨
      -ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ ModularCurve.infSubgroup p M H hpM)
    :
    ∃ W : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) ≃ₗ[K] ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p),

      (∀ (f : CuspForm (CohCarrier.GammaH M H) 2)
          (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
          (pfW : PowerSeries ℤ), ModularCurve.IsIntegralQExp (ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f)) pfW →
          ∀ ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p), ((ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) =
              ρinf ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
                ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩) →
            ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) ((W ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) = ModularCurve.intSeriesC K pfW) ∧

      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M) (ω ω' : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)), ((ω' : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) = (haveI : NeZero (M / p) := ⟨Nat.pos_iff_ne_zero.mp (Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) hpM) (Fact.out : p.Prime).pos)⟩;
          haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
          AlgebraicCurve.Differential.correspondence (ModularCurve.heckeAlphaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) ℓ) (ModularCurve.heckeBetaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) ℓ)) ((ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) →
        ((W ω' : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) = ModularCurve.genDiffModL K p M H hpM S (CohCarrier.Gen.T ℓ hℓ hℓS hℓM) ((W ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K])) ∧

      (∀ (q' : ℕ) (hq : q'.Prime) (hqM : q' ∣ M) (_ : q' ≠ p) (ω ω' : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)), ((ω' : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) = (haveI : NeZero (M / p) := ⟨Nat.pos_iff_ne_zero.mp (Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) hpM) (Fact.out : p.Prime).pos)⟩;
          haveI : NeZero q' := ⟨hq.ne_zero⟩;
          AlgebraicCurve.Differential.correspondence (ModularCurve.heckeAlphaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) q') (ModularCurve.heckeBetaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) q')) ((ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) →
        ((W ω' : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) = ModularCurve.genDiffModL K p M H hpM S (CohCarrier.Gen.U q' hq hqM) ((W ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K])) ∧

      (∀ (d : (ZMod M)ˣ) (ω ω' : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)), ((ω' : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) = ModularCurve.genDiffModL K p M H hpM S (CohCarrier.Gen.dia d⁻¹) ((ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) →
        ((W ω' : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) = ModularCurve.genDiffModL K p M H hpM S (CohCarrier.Gen.dia d) ((W ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K])) ∧

      (∀ (ω ω' : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)), ((ω' : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) = ModularCurve.genDiffModL K p M H hpM S (CohCarrier.Gen.U p Fact.out hpM) ((ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) →
        ((W ω' : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) = ModularCurve.genDiffModL K p M H hpM S (CohCarrier.Gen.U p Fact.out hpM) ((W ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K])) ∧

      (∀ ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p), ((ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) ∈ AlgebraicCurve.regularDifferentials K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) ↔
        ((W ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) ∈ AlgebraicCurve.regularDifferentials K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))) := by sorry
