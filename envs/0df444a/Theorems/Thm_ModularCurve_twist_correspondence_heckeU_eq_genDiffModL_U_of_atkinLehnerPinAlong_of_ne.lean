-- Prove2me | Theorems.Thm_ModularCurve_twist_correspondence_heckeU_eq_genDiffModL_U_of_atkinLehnerPinAlong_of_ne
-- name    : ModularCurve.twist_correspondence_heckeU_eq_genDiffModL_U_of_atkinLehnerPinAlong_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/5db1e45a-dee9-50de-9f36-4e11f06d30cb
-- title:
--   Pinned twist carries the q-correspondence to U_q, q≠ p
-- statement:
--   Fix a prime $p$ and a positive integer $M$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image in $(\mathbb{Z}/(M/p))^\times$ is $1$, an algebraically closed field $K$ of characteristic $p$ with its $\mathbb{Z}/p$-algebra structure, and a set $S$ of naturals. Write $H'$ for the image of $H$ in $(\mathbb{Z}/(M/p))^\times$ ([`ModularCurve.infSubgroup`](def/ModularCurve_XHDifferentialsModL.html#L246)), $F'$ for the $q$-expansion function field [`ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) H')`](def/ModularCurve_X1.html#L101) and $\Omega^{\mathrm{ss}}$ for [`ModularCurve.ssPolarDifferentials`](def/ModularCurve_XHDifferentialsModL.html#L35), the $K$-submodule of $\Omega_{F'/K}$ of differentials regular outside the supersingular places and with at most simple poles there. Assume given: a $K$-linear map $\rho^\infty$ from $K \otimes_{\mathbb{Z}/p} (\,$the $\mathbb{Z}$-lattice [`CuspForm.twoCuspLattice M H 2 p ⊥`](def/CuspForm_TwoCuspLattice.html#L86) of weight-$2$ cusp forms on $\Gamma_H(M)$, reduced modulo $p)$ to $\Omega_{F'/K}$ which is an `IsInfReductionMap` (for $f$ in the two-cusp integral set with integral $q$-expansion power series $p_f$, the image of $\rho^\infty(1 \otimes \bar f)$ under `diffQExp` is the reduction of $p_f$ in $K((q))$) and whose range is exactly $\Omega^{\mathrm{ss}}$; an Atkin–Lehner datum `Wd` for $(M, M/p)$, i.e. $R$ with $M = (M/p)R$ and integers $a,b$ with $(M/p)a - Rb = 1$; a unit $e \in (\mathbb{Z}/M)^\times$ whose image $\bar e$ satisfies $\bar e\, \bar p = 1$ in $\mathbb{Z}/(M/p)$; a ring homomorphism $\varphi$ from the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ to $K$ with $\varphi(p) = 0$; and a $K$-linear automorphism $W$ of $\Omega^{\mathrm{ss}}$ pinned by the condition that for every $f$ in the two-cusp integral set, every $D$ with $p \nmid D$, every power series $P$ over that integral closure whose image in $\mathbb{C}[[q]]$ is the period-$1$ $q$-expansion of $D \cdot (\langle e \rangle f)\mid_2 \mathtt{Wd}$, and every $\omega \in \Omega^{\mathrm{ss}}$ with $\omega = \rho^\infty(1 \otimes \bar f)$, one has $D \cdot \mathrm{diffQExp}(W\omega) = \varphi(P)$ viewed in $K((q))$; finally assume that the $\omega$ so obtained span $\Omega^{\mathrm{ss}}$ over $K$. The conclusion is that for every prime $q' \mid M$ with $q' \ne p$ and all $\omega, \omega' \in \Omega^{\mathrm{ss}}$, if $\omega'$ is the image of $\omega$ under [`AlgebraicCurve.Differential.correspondence`](def/AlgebraicCurve_DifferentialPushPull.html#L69) applied to the pair (`heckeAlphaModLH`, `heckeBetaModLH`) at level $q'$, that is the trace along the inclusion $\alpha_{q'}$ of the pullback along $\beta_{q'}$, then $W\omega'$ equals [`ModularCurve.genDiffModL`](def/ModularCurve_XHDifferentialsModL.html#L266) at the generator $\mathtt{U}\,q'$ applied to $W\omega$, which for $q' \ne p$ is the opposite composite $\mathrm{tr}_{\beta_{q'}} \circ \alpha_{q'}^{*}$.
--
--   This is the Atkin–Lehner twisting step on supersingular-polar differentials in characteristic $p$: a twist determined by an Atkin–Lehner datum at $(M, M/p)$ and the diamond operator $\langle e \rangle$ conjugates the transposed Hecke correspondence at a prime $q' \mid M$, $q' \ne p$, into the operator $U_{q'}$ of the mod-$p$ generator family. It is used in the construction of the twisting isomorphism of $\Omega^{\mathrm{ss}}$ intertwining the whole transposed Hecke action, [`ModularCurve.exists_linearEquiv_ssPolarDifferentials_twist_transposeHecke_genDiffModL_of_isInfReductionMap_of_mem_infSubgroup`](thm.html#ModularCurve.exists_linearEquiv_ssPolarDifferentials_twist_transposeHecke_genDiffModL_of_isInfReductionMap_of_mem_infSubgroup).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_twist_correspondence_heckeU_eq_genDiffModL_U_of_atkinLehnerPinAlong_of_ne.lean

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

theorem ModularCurve.twist_correspondence_heckeU_eq_genDiffModL_U_of_atkinLehnerPinAlong_of_ne
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p] [Algebra (ZMod p) K] (S : Set ℕ)

    (ρinf : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p →ₗ[K] Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K])
    (hρinf : ModularCurve.IsInfReductionMap K p M H hpM ρinf)
    (hrange : LinearMap.range ρinf = ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)

    (Wd : ModularForm.AtkinLehnerDatum M (M / p))
    (e : (ZMod M)ˣ) (he : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1)

    (φ : ↥(integralClosure ℤ ℂ) →+* K) (hφ : φ (p : ↥(integralClosure ℤ ℂ)) = 0)

    (W : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) ≃ₗ[K] ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p))
    (hW :
      ∀ (f : CuspForm (CohCarrier.GammaH M H) 2)
          (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
          (D : ℕ) (_ : ¬ p ∣ D)
          (pfW : PowerSeries ↥(integralClosure ℤ ℂ)),
          pfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
            UpperHalfPlane.qExpansion 1 ((D : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f)) →
          ∀ ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p), ((ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) =
              ρinf ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
                ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩) →
            (D : K) • ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) ((W ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) =
              HahnSeries.ofPowerSeries ℤ K (pfW.map φ))

    (hspan : Submodule.span K {ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) |
        ∃ (f : CuspForm (CohCarrier.GammaH M H) 2) (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
          (D : ℕ) (_ : ¬ p ∣ D) (pfW : PowerSeries ↥(integralClosure ℤ ℂ)),
          pfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
            UpperHalfPlane.qExpansion 1 ((D : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f)) ∧
          ((ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) =
            ρinf ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
              ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩)} = ⊤)
    :

      (∀ (q' : ℕ) (hq : q'.Prime) (hqM : q' ∣ M) (_ : q' ≠ p) (ω ω' : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)), ((ω' : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) = (haveI : NeZero (M / p) := ⟨Nat.pos_iff_ne_zero.mp (Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) hpM) (Fact.out : p.Prime).pos)⟩;
          haveI : NeZero q' := ⟨hq.ne_zero⟩;
          AlgebraicCurve.Differential.correspondence (ModularCurve.heckeAlphaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) q') (ModularCurve.heckeBetaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) q')) ((ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) →
        ((W ω' : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) = ModularCurve.genDiffModL K p M H hpM S (CohCarrier.Gen.U q' hq hqM) ((W ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K])) := by sorry
