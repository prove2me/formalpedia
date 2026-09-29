-- Prove2me | Theorems.Thm_ModularCurve_exists_isFrobPushDiff_qExpFunctionFieldC_gammaH
-- name    : ModularCurve.exists_isFrobPushDiff_qExpFunctionFieldC_gammaH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/6534eb2c-772f-5ec2-ad8d-8e1f058ffbeb
-- title:
--   Frobenius push-forward on differentials of X_{H'}(N) in characteristic p
-- statement:
--   Let $p$ be a prime, let $K$ be an algebraically closed field carrying an algebra structure over $\mathbb{Z}/p$ (so $K$ has characteristic $p$), let $N \geq 1$ and let $H' \leq (\mathbb{Z}/N)^{\times}$ be a subgroup. Write $\Gamma_{H'}(N) \leq \mathrm{SL}_2(\mathbb{Z})$ for the image under the inclusion $\Gamma_0(N) \hookrightarrow \mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H'$ under the homomorphism $\Gamma_0(N) \to (\mathbb{Z}/N)^{\times}$ sending $\gamma$ to its lower right entry mod $N$, and let $F =$ `qExpFunctionFieldC K (CohCarrier.GammaH N H')` be the intermediate field of $K(\!(q)\!)$ generated over $K$ by all quotients $\iota(p_f)/\iota(p_g)$, where $f, g$ are modular forms of some weight $k$ for $\Gamma_{H'}(N)$ admitting integral $q$-expansions $p_f, p_g \in \mathbb{Z}[\![q]\!]$, the coefficientwise image $\iota(p_g)$ in $K(\!(q)\!)$ being nonzero. The assertion is the existence of a $K$-linear endomorphism $C$ of $\Omega_{F/K}$ such that for every $\omega \in \Omega_{F/K}$ the $q$-expansion $\Theta =$ `diffQExp F` $\colon \Omega_{F/K} \to K(\!(q)\!)$ (the $F$-linear map induced by the $q$-expansion derivation on $F$) satisfies $\Theta(C\omega) =$ `qDecimate K p` $(\Theta(\omega))$, i.e. the $n$-th coefficient of $\Theta(C\omega)$ is the $pn$-th coefficient of $\Theta(\omega)$ for all $n \in \mathbb{Z}$.
--
--   Classically $C$ is the composite of the Cartier operator of the one-variable function field $F/K$ with the coefficientwise Frobenius, whose effect on $q$-expansions at $\infty$ is the decimation $a_n \mapsto a_{pn}$; this existence statement is what identifies the project's unconditionally defined Frobenius push-forward operator with the genuine one. It is used in the study of cuspidal and regular differentials with prescribed $q$-expansions and in the mod-$p$ compatibility between $U_p$ and this operator on the component through the cusp $\infty$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_isFrobPushDiff_qExpFunctionFieldC_gammaH.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.exists_isFrobPushDiff_qExpFunctionFieldC_gammaH
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [IsAlgClosed K] [Algebra (ZMod p) K]
    (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ∃ C : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K] →ₗ[K]
        Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K],
      ModularCurve.IsFrobPushDiff K (CohCarrier.GammaH N H') p C := by sorry
