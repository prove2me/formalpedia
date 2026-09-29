-- Prove2me | Theorems.Thm_ModularCurve_coeff_trace_along_heckeBetaModLH_of_not_dvd
-- name    : ModularCurve.coeff_trace_along_heckeBetaModLH_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/e2ed5b99-9742-5f53-98ac-9b4163899022
-- title:
--   Trace along q↦ q^ℓ of q-expansions, ℓ∤ N
-- statement:
--   Let $K$ be an algebraically closed field, $N\ge 1$, $H'$ a subgroup of $(\mathbb{Z}/N)^{\times}$ and $\ell$ a prime coprime to $N$, with $N$ and $\ell$ both nonzero in $K$. Write $F=$ `qExpFunctionFieldC K (GammaH N H')` and $F'=$ `qExpFunctionFieldC K (GammaH N H' ⊓ Gamma0 (N*ℓ))`, the intermediate fields of $K((q))$ generated over $K$ by the quotients $\mathrm{intSeriesC}(p_f)/\mathrm{intSeriesC}(p_g)$ of integral $q$-expansions of modular forms of equal weight for the respective groups. Assume: the substitution $q\mapsto q^{\ell}$ carries $F$ into $F'$ (so that `heckeBetaModLH` is this substitution $\beta\colon F\to F'$, rather than the default inclusion $\alpha$); there exists a homomorphism $\rho$ from $\Gamma_0(N)$ to the $K$-algebra automorphisms of $F$ satisfying `IsDiamondPullbackModL`, i.e. $\rho(\gamma)$ sends the class of $p_{f_1}/p_{g_1}$ to that of $p_f/p_g$ whenever $f_1,g_1$ are the weight-$k$ slash-translates of $f,g$ by $\gamma$; and $W$ is a $K$-algebra automorphism of $F'$ with $W\circ\beta=\alpha$ and $W\circ\alpha=\beta\circ\langle\ell\rangle^{-1}$, where $\langle\ell\rangle^{-1}$ is `diamondActionModL` evaluated at a lift to $\Gamma_0(N)$ of $(\ell\bmod N)^{-1}$. Then for all $v\in F'$ and $n\in\mathbb{Z}$, viewing $F'$ as an $F$-algebra through $\beta$, the $n$-th Laurent coefficient of $\operatorname{Tr}_{F'/F}(v)\in F\subseteq K((q))$ equals $\ell\cdot v_{n\ell}+(Wv)_n$.
--
--   This is the function-field form of the $q$-expansion formula for the Hecke operator $T_\ell$ in the case $\ell\nmid N$, the trace along $q\mapsto q^{\ell}$ splitting into the $\ell$ conjugates $v(\zeta_\ell^{j}q)$ and the Atkin–Lehner term $(Wv)(q^{\ell})$. It is used to compute the action of the Hecke correspondence on $q$-expansions of differentials, in [`ModularCurve.coeff_diffQExp_heckeDiffModLH_of_not_dvd_of_charP`](thm.html#ModularCurve.coeff_diffQExp_heckeDiffModLH_of_not_dvd_of_charP).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coeff_trace_along_heckeBetaModLH_of_not_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.coeff_trace_along_heckeBetaModLH_of_not_dvd
    (K : Type*) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hcop : ℓ.Coprime N) (hNK : ((N : ℕ) : K) ≠ 0) (hℓK : ((ℓ : ℕ) : K) ≠ 0)
    (hβ : ModularCurve.HeckeBetaModLHDefined K N H' ℓ)
    (hdia : ∃ ρ : CongruenceSubgroup.Gamma0 N →*
        (↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) ≃ₐ[K] ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))),
      ModularCurve.IsDiamondPullbackModL K N H' ρ)
    (W : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))) ≃ₐ[K]
        ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))))
    (hWβ : ∀ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')),
        W (ModularCurve.heckeBetaModLH K N H' ℓ x) = ModularCurve.heckeAlphaModLH K N H' ℓ x)
    (hWα : ∀ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')),
        W (ModularCurve.heckeAlphaModLH K N H' ℓ x) =
          ModularCurve.heckeBetaModLH K N H' ℓ
            (ModularCurve.diamondActionModL K N H'
              (CuspForm.gammaLift N (ZMod.unitOfCoprime ℓ hcop)⁻¹) x))
    (v : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)))) (n : ℤ) :
    (((letI := AlgebraicCurve.algebraAlong (ModularCurve.heckeBetaModLH K N H' ℓ);
        Algebra.trace ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))
          ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))) v) :
        ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))) : LaurentSeries K).coeff n =
      (ℓ : K) * (v : LaurentSeries K).coeff (n * ℓ) +
        ((W v : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)))) :
          LaurentSeries K).coeff n := by sorry
