-- Prove2me | Theorems.Thm_ModularCurve_coeff_trace_along_heckeBetaModLH_of_dvd
-- name    : ModularCurve.coeff_trace_along_heckeBetaModLH_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/e15bb68a-d5a3-59f5-8736-49f514812680
-- title:
--   Trace along q↦ q^ℓ on q-expansions when ℓ∣ N
-- statement:
--   Let $K$ be an algebraically closed field, $N\ge 1$ with $(N:K)\neq 0$, let $H'$ be a subgroup of $(\mathbb{Z}/N)^{\times}$ and let $\ell$ be a prime dividing $N$. Write $\Gamma_{H'}$ for the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ obtained as the image in $\mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H'$ under the lower-right-entry character $\Gamma_0(N)\to(\mathbb{Z}/N)^{\times}$, and let $F=$ `qExpFunctionFieldC K (CohCarrier.GammaH N H')` and $F'=$ `qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))` be the subfields of $K((q))$ generated over $K$ by the ratios $\bar p_f/\bar p_g$ of reductions to $K$ of integral $q$-expansions of modular forms of equal weight for the respective groups. Assume `HeckeBetaModLHDefined K N H' ℓ`, i.e. that the substitution $q\mapsto q^{\ell}$ (the ring map scaling Laurent exponents by $\ell$) carries $F$ into $F'$; then `heckeBetaModLH` is that substitution, viewed as a $K$-algebra map $F\to F'$, and $F'$ is regarded as an $F$-algebra through it. The assertion is that for every $v\in F'$ and every $n\in\mathbb{Z}$, the $q^{n}$-coefficient of $\mathrm{Tr}_{F'/F}(v)$, computed as an element of $K((q))$, equals $\ell$ times the $q^{n\ell}$-coefficient of $v$.
--
--   This is the $q$-expansion formula for the trace along the degeneracy map $q\mapsto q^{\ell}$ in the case $\ell\mid N$, where the extension has degree $\ell$ and the conjugates of $v$ are its twists $v(\zeta_\ell^{j}q)$, so that the trace picks out the coefficients in arithmetic progressions of step $\ell$. It is used in the corresponding coefficient computation for differentials, [`ModularCurve.coeff_diffQExp_heckeDiffModLH_of_dvd`](thm.html#ModularCurve.coeff_diffQExp_heckeDiffModLH_of_dvd), in the construction of the mod-$\ell$ Hecke action on differentials of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coeff_trace_along_heckeBetaModLH_of_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.coeff_trace_along_heckeBetaModLH_of_dvd
    (K : Type*) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ℓ ∣ N) (hNK : ((N : ℕ) : K) ≠ 0)
    (hβ : ModularCurve.HeckeBetaModLHDefined K N H' ℓ)
    (v : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)))) (n : ℤ) :
    (((letI := AlgebraicCurve.algebraAlong (ModularCurve.heckeBetaModLH K N H' ℓ);
        Algebra.trace ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))
          ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))) v) :
        ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))) : LaurentSeries K).coeff n =
      (ℓ : K) * (v : LaurentSeries K).coeff (n * ℓ) := by sorry
