-- Prove2me | Theorems.Thm_ModularCurve_coeff_diffQExp_heckeDiffModLH_of_dvd
-- name    : ModularCurve.coeff_diffQExp_heckeDiffModLH_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/620edc22-7e3e-5380-bd98-e98dd4424d13
-- title:
--   q-expansion of U_ℓ on differentials for ℓ ∣ N
-- statement:
--   Let $K$ be an algebraically closed field, $N \ge 1$, $H'$ a subgroup of $(\mathbb{Z}/N)^\times$, and $\ell \ge 1$ a prime with $\ell \mid N$ and $N \ne 0$ in $K$. Write $\Gamma_{H'}(N)$ for the subgroup [`CohCarrier.GammaH N H'`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}_2(\mathbb{Z})$, the image of the preimage of $H'$ under the character $\Gamma_0(N) \to (\mathbb{Z}/N)^\times$ sending a matrix to the reduction of its lower right entry, and let $F =$ [`ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')`](def/ModularCurve_X1.html#L101) be the intermediate field of $K((q))$ obtained by adjoining to $K$ all quotients $\iota(p_f)/\iota(p_g)$ coming from integral $q$-expansions $p_f, p_g \in \mathbb{Z}[[q]]$ of modular forms $f, g$ of some common weight for $\Gamma_{H'}(N)$, with $\iota(p_g) \ne 0$, where $\iota$ denotes the coefficientwise image in $K((q))$. Put $F' =$ [`ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ Gamma0 (N * ℓ))`](def/ModularCurve_X1.html#L101), and assume [`ModularCurve.HeckeBetaModLHDefined K N H' ℓ`](def/ModularCurve_XHDifferentialsModL.html#L143), i.e. that the substitution $q \mapsto q^\ell$ on Laurent series carries $F$ into $F'$; then [`ModularCurve.heckeBetaModLH`](def/ModularCurve_XHDifferentialsModL.html#L167) is that substitution $\beta : F \to F'$, while [`ModularCurve.heckeAlphaModLH`](def/ModularCurve_XHDifferentialsModL.html#L132) is the inclusion $\alpha : F \hookrightarrow F'$. Let [`ModularCurve.heckeDiffModLH`](def/ModularCurve_XHDifferentialsModL.html#L185) be the $K$-linear endomorphism $\omega \mapsto \mathrm{tr}_\beta(\alpha^*\omega)$ of $\Omega_{F/K}$, and let $\Theta =$ [`ModularCurve.diffQExp`](def/ModularCurve_HeckeDifferential.html#L128) be the $F$-linear map $\Omega_{F/K} \to K((q))$ lifting the derivation $q\,\mathrm{d}/\mathrm{d}q$ of $K((q))$ restricted along $F$. Then for every $\omega \in \Omega_{F/K}$ and every $n \in \mathbb{Z}$, the $n$-th Laurent coefficient of $\Theta(\mathrm{tr}_\beta(\alpha^*\omega))$ equals the $n\ell$-th Laurent coefficient of $\Theta(\omega)$.
--
--   This is the $q$-expansion formula for the Atkin operator $U_\ell$ at a prime $\ell$ dividing the level, acting on the Kähler differentials of $X_{H'}(N)$ in the guise of its $q$-expansion function field over an algebraically closed field of characteristic not dividing $N$: on $q$-expansions of differentials, $\sum_n a_n q^n \mapsto \sum_n a_{n\ell} q^n$. It is used in the comparison of the correspondence $(\alpha, \beta)$ with the action on differentials coming from integral $q$-expansions, and in the analysis of the induced map when the two pullbacks differ.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coeff_diffQExp_heckeDiffModLH_of_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem ModularCurve.coeff_diffQExp_heckeDiffModLH_of_dvd
    (K : Type*) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ)
    (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N) (hNK : ((N : ℕ) : K) ≠ 0)
    (hβ : ModularCurve.HeckeBetaModLHDefined K N H' ℓ)
    (ω : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K]) (n : ℤ) :
    (ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) (ModularCurve.heckeDiffModLH K N H' ℓ ω)).coeff n =
      (ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) ω).coeff (n * ℓ) := by sorry
